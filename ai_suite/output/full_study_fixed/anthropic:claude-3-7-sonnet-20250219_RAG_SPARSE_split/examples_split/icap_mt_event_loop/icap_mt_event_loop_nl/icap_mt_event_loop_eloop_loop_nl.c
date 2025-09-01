// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;

/***
 * Description:
The eloop_handler function pointer that handles the data of an event loop and preserves the property of event loop and data.

@param data: the data to be handled, which needs to preserve some property before and after the execution of handler.
*/
typedef void eloop_handler(void *data);

/*@
// Predicate family for the handler function
predicate_family eloop_handler_pre(void *handler)(void *data);
predicate_family eloop_handler_post(void *handler)(void *data);

// Predicate for the event loop
predicate eloop_inv(eloop x, predicate() I);

// Predicate for the locked event loop
predicate locked_eloop(eloop x, predicate() I);

// Predicate for the event loop structure
predicate eloop_struct(eloop x; int signalCount, eloop_handler *handler, void *handlerData, predicate() I) =
    x != 0 &*&
    x->signalCount |-> signalCount &*&
    x->handler |-> handler &*&
    x->handlerData |-> handlerData &*&
    is_eloop_handler(handler) == true &*&
    malloc_block_eloop(x) &*&
    I();
@*/


struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    void *handlerData;
};

/*@
// Define the lock invariant for the event loop
predicate_ctor eloop_lock_inv(eloop x, predicate() I)() =
    eloop_struct(x, ?signalCount, ?handler, ?handlerData, I);
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
//@ requires eloop_inv(x, ?I);
//@ ensures false; // Function never returns due to infinite loop
{
    for (;;)
    //@ invariant eloop_inv(x, I);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        //@ open eloop_inv(x, I);
        acquire(&x->lock);
        //@ open eloop_lock_inv(x, I)();
        //@ open eloop_struct(x, ?signalCount, ?h, ?data, I);
        
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler)
                handlerData = x->handlerData;
        }
        
        //@ close eloop_struct(x, x->signalCount, x->handler, x->handlerData, I);
        //@ close eloop_lock_inv(x, I)();
        release(&x->lock);
        //@ close eloop_inv(x, I);
        
        if (handler) {
            //@ open eloop_inv(x, I);
            //@ assert I();
            //@ close eloop_handler_pre(handler)(handlerData);
            handler(handlerData);
            //@ open eloop_handler_post(handler)(handlerData);
            //@ assert I();
            //@ close eloop_inv(x, I);
        }
    }
}