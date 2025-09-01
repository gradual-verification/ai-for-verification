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


void eloop_loop(eloop x)
    //@ requires eloop(x);
    //@ ensures eloop(x);
{
    for (;;)
        //@ invariant eloop(x);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        //@ open eloop(x);
        acquire(&x->lock);
        //@ open I(x)();
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler) {
                handlerData = x->handlerData;
                //@ assert [_]is_eloop_handler(handler, x, ?dataPred);
                //@ assert [_]dataPred(handlerData);
            }
        }
        //@ close I(x)();
        release(&x->lock);
        //@ close eloop(x);
        
        if (handler) {
            //@ assert [_]is_eloop_handler(handler, x, ?dataPred2);
            //@ assert [_]dataPred2(handlerData);
            handler(handlerData);
        }
    }
}