// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"

typedef struct eloop *eloop;

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

typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);

eloop eloop_create()
    //@ requires true;
    //@ ensures eloop(result);
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    //@ close I(x)();
    //@ close exists(I(x));
    init(&x->lock);
    //@ leak lock(&x->lock, _) &*& malloc_block_eloop(x);
    release(&x->lock);
    //@ close eloop(x);
    return x;
}

void eloop_loop(eloop x)
    //@ requires eloop(x);
    //@ ensures eloop(x);
{
    for (;;)
        //@ invariant eloop(x);
    {
        //@ open eloop(x);
        eloop_handler *handler = 0;
        void *handlerData;
        
        acquire(&x->lock);
        //@ open I(x)();
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler)
                handlerData = x->handlerData;
        }
        //@ close I(x)();
        release(&x->lock);
        //@ close eloop(x);
        
        if (handler)
            handler(handlerData);
        
    }
}

void eloop_signal(eloop x)
    //@ requires eloop(x);
    //@ ensures eloop(x);
{
    //@ open eloop(x);
    acquire(&x->lock);
    //@ open I(x)();
    if (x->signalCount == INT_MAX) abort();
    x->signalCount++;
    //@ close I(x)();
    release(&x->lock);
    //@ close eloop(x);
}

void eloop_when(eloop x, eloop_handler *h, void *data)
    //@ requires eloop(x) &*& h == 0 ? true : [_]is_eloop_handler(h, x, ?dataPred) &*& [_]dataPred(data);
    //@ ensures eloop(x);
{
    //@ open eloop(x);
    acquire(&x->lock);
    //@ open I(x)();
    x->handler = h;
    x->handlerData = data;
    //@ if (h) { assert [_]is_eloop_handler(h, x, ?dataPred); x->dataPred = dataPred; }
    //@ close I(x)();
    release(&x->lock);
    //@ close eloop(x);
}