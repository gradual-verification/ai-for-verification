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


struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    void *handlerData;
};

/*@

// The property of the data handled by the event loop handler.
// This is a predicate family indexed by the handler function pointer,
// allowing different handlers to have different data properties.
predicate_family eloop_handler_inv(void* func)(void* data);

// A contract for the eloop_handler function pointer type.
// It requires and ensures the data property, modeling the "preservation" aspect.
typedef void eloop_handler_contract(void *data);
    requires eloop_handler_inv(this)(data);
    ensures eloop_handler_inv(this)(data);

// A recursive predicate representing a collection of 'count' pending jobs.
// Each job is represented by a chunk of the handler's invariant.
predicate jobs(int count, eloop_handler* h, void* data) =
    count <= 0 ?
        true
    :
        eloop_handler_inv(h)(data) &*& jobs(count - 1, h, data);

// The lock invariant for the event loop's lock.
// It protects the shared fields: signalCount, handler, and handlerData.
// It also owns the 'jobs' predicate, tying the number of pending job resources
// to the signalCount.
predicate eloop_inv(eloop x) =
    x->signalCount |-> ?sc &*&
    x->handler |-> ?h &*&
    x->handlerData |-> ?d &*&
    0 <= sc &*&
    (h == 0 ? true : is_eloop_handler_contract(h) == true &*& jobs(sc, h, d));

// The main predicate for an event loop structure.
// It owns the memory block of the struct and the lock itself.
predicate eloop_pred(eloop x) =
    malloc_block_eloop(x) &*&
    x->lock |-> _ &*&
    lock(&x->lock, eloop_inv(x));

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
    //@ requires [?f]eloop_pred(x);
    //@ ensures false;
{
    for (;;)
        //@ invariant [f]eloop_pred(x);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        //@ open eloop_pred(x);
        acquire(&x->lock);
        //@ open eloop_inv(x)();
        
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler) {
                handlerData = x->handlerData;
                //@ open jobs(x->signalCount + 1, handler, handlerData);
            }
        }
        
        //@ close eloop_inv(x)();
        release(&x->lock);
        
        //@ close [f]eloop_pred(x);
        
        if (handler) {
            handler(handlerData);
            //@ leak eloop_handler_inv(handler)(handlerData);
        }
    }
}