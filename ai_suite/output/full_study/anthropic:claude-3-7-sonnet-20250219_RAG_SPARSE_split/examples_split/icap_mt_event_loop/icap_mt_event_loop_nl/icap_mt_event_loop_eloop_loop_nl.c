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

/*@
// Define a predicate for the event loop
predicate eloop_inv(eloop x, predicate() P) =
    x->signalCount |-> ?count &*&
    x->handler |-> ?handler &*&
    x->handlerData |-> ?data &*&
    count >= 0 &*&
    (handler != 0 ? is_eloop_handler(handler) == true : true);

// Define a predicate for the lock invariant
predicate_ctor eloop_lock_inv(eloop x, predicate() P)() =
    eloop_inv(x, P) &*&
    (x->signalCount > 0 && x->handler != 0 ? [1/2]P() : emp);

// Define a predicate for the event loop structure
predicate event_loop(eloop x, predicate() P) =
    malloc_block_eloop(x) &*&
    lock(&x->lock, eloop_lock_inv(x, P)) &*&
    [1/2]P();
@*/

// TODO: make this function pass the verification
/***
 * Description:
The eloop_loop function runs the given event loop infinitely and makes sure that the property of that event loop is unchanged.
It has a forever loop, and does the following things in the loop: acquiring the lock, getting the handler and data (if the signal count > 0),
releasing the lock and handling the data (if the handler is found.)

@param x: the event loop instance to be run.

It makes sure that x presevees the property of event loop before and after the execution.
*/
void eloop_loop(eloop x)
//@ requires event_loop(x, ?P);
//@ ensures false; // Function never returns due to infinite loop
{
    for (;;)
    //@ invariant event_loop(x, P);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        //@ open event_loop(x, P);
        acquire(&x->lock);
        //@ open eloop_lock_inv(x, P)();
        //@ open eloop_inv(x, P);
        
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler)
                handlerData = x->handlerData;
        }
        
        //@ close eloop_inv(x, P);
        //@ close eloop_lock_inv(x, P)();
        release(&x->lock);
        //@ close event_loop(x, P);
        
        if (handler) {
            //@ assert is_eloop_handler(handler) == true;
            //@ assert [1/2]P();
            handler(handlerData);
            //@ assert [1/2]P();
        }
    }
}