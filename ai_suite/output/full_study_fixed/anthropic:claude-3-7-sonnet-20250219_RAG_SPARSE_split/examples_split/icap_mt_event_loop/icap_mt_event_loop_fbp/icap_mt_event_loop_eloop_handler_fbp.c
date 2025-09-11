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

// Implementation of eloop_handler function
void handle_signal(eloop x, void *data)
    //@ requires eloop(x) &*& [_]x->dataPred(data);
    //@ ensures eloop(x) &*& [_]x->dataPred(data);
{
    //@ open eloop(x);
    acquire(&x->lock);
    //@ open I(x)();
    
    eloop_handler *h = x->handler;
    //@ predicate(void *) dataPred = x->dataPred;
    
    if (h != 0) {
        void *handlerData = x->handlerData;
        x->signalCount++;
        
        //@ close I(x)();
        release(&x->lock);
        
        h(handlerData);
        
        acquire(&x->lock);
        //@ open I(x)();
        x->signalCount--;
    }
    
    //@ close I(x)();
    release(&x->lock);
    //@ close eloop(x);
}