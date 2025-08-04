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

// We add the assumption that the data predicate is pure. This allows the proof to go through
// by treating the data predicate as a fact that can be learned inside the lock and used outside.
predicate_ctor I(eloop x)() =
    x->signalCount |-> ?signalCount &*& 0 <= signalCount &*&
    x->handler |-> ?h &*&
    x->dataPred |-> ?dataPred &*&
    h == 0 ?
        x->handlerData |-> _
    :
        x->handlerData |-> ?data &*&
        [_]is_eloop_handler(h, x, dataPred) &*&
        is_pure(dataPred) == true &*& // Assume the data predicate is pure
        dataPred(data);

predicate eloop(eloop x) =
    [_]lock(&x->lock, I(x));
@*/


typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);
    


// TODO: make this function pass the verification
void eloop_loop(eloop x)
    //@ requires eloop(x);
    //@ ensures false; // A non-terminating function does not satisfy its postcondition.
{
    for (;;)
        //@ invariant eloop(x);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        //@ open eloop(x);
        acquire(&x->lock);
        //@ close eloop(x);
        
        //@ open I(x)();
        
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler) {
                handlerData = x->handlerData;
                //@ assert x->dataPred |-> ?dp &*& is_pure(dp) == true &*& dp(handlerData);
            }
        }
        
        //@ close I(x)();
        release(&x->lock);
        
        if (handler) {
            // The pure fact `dp(handlerData)` persists outside the lock.
            // Since dp is pure, `[_]dp(handlerData)` is equivalent to `dp(handlerData)`.
            //@ open [_]x->dataPred(handlerData);
            handler(handlerData);
            //@ close [_]x->dataPred(handlerData);
        }
    }
}
