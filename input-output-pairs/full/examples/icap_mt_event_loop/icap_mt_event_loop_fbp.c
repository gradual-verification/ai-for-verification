// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "../multi-files/shared_boxes/gotsmanlock.h"

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

eloop eloop_create()
    //@ requires true;
    //@ ensures eloop(result);
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    init(&x->lock);
    release(&x->lock);
    return x;
}

void eloop_loop(eloop x)
    //@ requires eloop(x);
    //@ ensures eloop(x);
{
    for (;;)
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        acquire(&x->lock);
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler)
                handlerData = x->handlerData;
        }
        release(&x->lock);
        
        if (handler)
            handler(handlerData);
        
    }
}

void eloop_signal(eloop x)
    //@ requires eloop(x);
    //@ ensures eloop(x);
{
    acquire(&x->lock);
    if (x->signalCount == INT_MAX) abort();
    x->signalCount++;
    release(&x->lock);
}

void eloop_when(eloop x, eloop_handler *h, void *data)
    //@ requires eloop(x) &*& h == 0 ? true : [_]is_eloop_handler(h, x, ?dataPred) &*& [_]dataPred(data);
    //@ ensures eloop(x);
{
    acquire(&x->lock);
    x->handler = h;
    x->handlerData = data;
    release(&x->lock);
}