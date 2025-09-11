// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;


typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);


struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    //@ predicate(void *) dataPred;
    void *handlerData;
};

/*@

predicate_ctor I(eloop x)() =
    x->signalCount |-> ?signalCount &*& 0 <= signalCount &*&
    x->handler |-> ?h &*&
    x->dataPred |-> ?dataPred &*&
    h == 0 ?
        x->handlerData |-> _ &*&
        true
    :
        x->handlerData |-> ?data &*&
        [_]is_eloop_handler(h, x, dataPred) &*& [_]dataPred(data);

predicate eloop(eloop x) =
    [_]lock(&x->lock, I(x));
@*/

// TODO: make this function pass the verification
void signal(eloop x)
    //@ requires eloop(x);
    //@ ensures eloop(x);
{
    //@ open eloop(x);
    acquire(&x->lock);
    //@ open I(x)();
    
    x->signalCount++;
    
    eloop_handler *h = x->handler;
    if (h != 0) {
        //@ predicate(void *) dataPred = x->dataPred;
        void *data = x->handlerData;
        //@ close I(x)();
        release(&x->lock);
        h(data);
        //@ open eloop(x);
        acquire(&x->lock);
        //@ open I(x)();
    }
    
    //@ close I(x)();
    release(&x->lock);
    //@ close eloop(x);
}

void set_handler(eloop x, eloop_handler *h, void *data)
    //@ requires eloop(x) &*& h == 0 ? true : [_]is_eloop_handler(h, x, ?dataPred) &*& [_]dataPred(data);
    //@ ensures eloop(x);
{
    //@ open eloop(x);
    acquire(&x->lock);
    //@ open I(x)();
    
    x->handler = h;
    if (h == 0) {
        x->handlerData = 0;
        //@ x->dataPred = (predicate(void *))0;
    } else {
        x->handlerData = data;
        //@ x->dataPred = dataPred;
    }
    
    //@ close I(x)();
    release(&x->lock);
    //@ close eloop(x);
}

eloop create_eloop()
    //@ requires true;
    //@ ensures eloop(result);
{
    eloop result = malloc(sizeof(struct eloop));
    if (result == 0) abort();
    
    result->signalCount = 0;
    result->handler = 0;
    result->handlerData = 0;
    
    //@ close I(result)();
    //@ close exists<predicate()>(I(result));
    init(&result->lock);
    //@ close I(result)();
    release(&result->lock);
    //@ close eloop(result);
    
    return result;
}

void dispose_eloop(eloop x)
    //@ requires eloop(x);
    //@ ensures true;
{
    //@ open eloop(x);
    acquire(&x->lock);
    //@ open I(x)();
    finalize(&x->lock);
    free(x);
}