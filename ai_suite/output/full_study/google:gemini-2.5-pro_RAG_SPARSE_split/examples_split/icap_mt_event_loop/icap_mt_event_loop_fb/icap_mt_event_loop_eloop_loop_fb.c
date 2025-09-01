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
void eloop_loop(eloop x)
    //@ requires eloop(x);
    //@ ensures eloop(x);
{
    for (;;)
        //@ invariant eloop(x);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        //@ predicate(void *) dataPred = 0;
        
        acquire(&x->lock);
        //@ open I(x)();
        
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler) {
                // A handler is available. Prepare to call it.
                // We need to extract the handler's data predicate from the lock invariant.
                // To do this, we temporarily set the handler to null in the shared state.
                //@ dataPred = x->dataPred;
                handlerData = x->handlerData;
                x->handler = 0;
                
                // Now, we can close the invariant. The data predicate chunk is now outside the lock.
                //@ close I(x)();
            } else {
                // No handler, just close the invariant.
                //@ close I(x)();
            }
        } else {
            // No signal, just close the invariant.
            //@ close I(x)();
        }
        
        release(&x->lock);
        
        if (handler) {
            // The handler was extracted. Call it.
            // We have eloop(x) from the loop invariant.
            // We have [_]dataPred(handlerData) because we extracted it.
            // We have [_]is_eloop_handler(handler, x, dataPred) because it was in the invariant.
            // These satisfy the handler's precondition.
            //@ assert [_]is_eloop_handler(handler, x, dataPred);
            //@ assert [_]dataPred(handlerData);
            handler(handlerData);
            
            // The handler call returns eloop(x) and [_]dataPred(handlerData).
            // Now, we must return the data predicate to the lock invariant.
            acquire(&x->lock);
            //@ open I(x)();
            
            // At this point, x->handler is 0, as we set it before.
            // Restore the original handler.
            x->handler = handler;
            
            // Now we can close the invariant again, this time consuming the data predicate.
            //@ close I(x)();
            release(&x->lock);
        }
        // If no handler was called, the loop invariant eloop(x) already holds.
    }
}