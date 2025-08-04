// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;

struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    void *handlerData;
};


/***
 * Description:
The eloop_handler function pointer that handles the data of an event loop and preserves the property of event loop and data.

@param data: the data to be handled, which needs to preserve some property before and after the execution of handler.
*/
typedef void eloop_handler(void *data);
//@ predicate_family eloop_handler_pred(eloop_handler* h)(void* data);
/*@
// We specify the handler's contract here. It requires a duplicable chunk
// representing the property of the data, and ensures it is preserved.
predicate is_eloop_handler(eloop_handler* h) =
    forall (void* data)
    requires [_]eloop_handler_pred(h)(data);
    ensures [_]eloop_handler_pred(h)(data);
@*/

/*@
// The lock invariant. It protects the fields of the eloop struct.
// The eloop_handler_pred is marked as duplicable `[_]`, meaning it's a pure property.
predicate eloop_inv(eloop x) =
    x->signalCount |-> ?sc &*&
    x->handler |-> ?h &*&
    x->handlerData |-> ?d &*&
    sc >= 0 &*&
    (h == 0 ? true : is_eloop_handler(h) &*& [_]eloop_handler_pred(h)(d));

// The main predicate for an eloop instance. It owns the memory for the struct
// and the lock that protects its invariant.
predicate eloop_spec(eloop x) =
    x != 0 &*&
    malloc_block_eloop(x) &*&
    x->lock |-> _ &*&
    lock(&x->lock, eloop_inv(x));
@*/


/***
 * Description:
The eloop_loop function runs the given event loop infinitely and makes sure that the property of that event loop is unchanged.
It has a forever loop, and does the following things in the loop: acquiring the lock, getting the handler and data (if the signal count > 0),
releasing the lock and handling the data (if the handler is found.)

@param x: the event loop instance to be run.

It makes sure that x presevees the property of event loop before and after the execution.
*/
void eloop_loop(eloop x)
    //@ requires [?f]eloop_spec(x);
    //@ ensures false;
{
    for (;;)
        //@ invariant [f]eloop_spec(x);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        //@ open eloop_spec(x);
        acquire(&x->lock);
        //@ open eloop_inv(x)();

        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler) {
                handlerData = x->handlerData;
                //@ open is_eloop_handler(handler);
                // Since the handler predicate is duplicable, we can duplicate it.
                // One copy remains in the lock invariant, the other is used for the call.
                //@ duplicate_chunk ([_]eloop_handler_pred(handler)(handlerData));
            }
        }
        
        //@ close eloop_inv(x)();
        release(&x->lock);
        //@ close [f]eloop_spec(x);
        
        if (handler) {
            handler(handlerData);
            // The duplicated chunk is consumed by the handler call, and a new one is produced.
            // This new chunk is implicitly leaked at the end of the loop iteration, which is acceptable.
        }
    }
}