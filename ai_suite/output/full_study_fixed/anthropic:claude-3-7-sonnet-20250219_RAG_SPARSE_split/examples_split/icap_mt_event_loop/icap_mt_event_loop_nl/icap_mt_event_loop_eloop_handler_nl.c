// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;

// TODO: make this function pass the verification
/***
 * Description:
The eloop_handler function pointer that handles the data of an event loop and preserves the property of event loop and data.

@param data: the data to be handled, which needs to preserve some property before and after the execution of handler.
*/
/*@
// Define a predicate family for the handler data
predicate_family eloop_handler_data(void *handler)(void *data);

// Define a predicate for the event loop
predicate eloop_inv(eloop e, void *handler, void *data) =
    e->lock |-> ?l &*&
    e->signalCount |-> ?count &*&
    e->handler |-> handler &*&
    e->handlerData |-> data &*&
    count > 0 ? [1/2]lock(l, eloop_inv(e, handler, data)) : emp;
@*/

typedef void eloop_handler(void *data);
//@ requires eloop_handler_data(this)(data);
//@ ensures eloop_handler_data(this)(data);


struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    void *handlerData;
};

/*@
// Define a predicate for the event loop structure
predicate eloop(struct eloop *e, void *handler, void *data) =
    malloc_block_eloop(e) &*&
    lock(&e->lock, eloop_inv(e, handler, data)) &*&
    e->signalCount |-> ?count &*&
    e->handler |-> handler &*&
    e->handlerData |-> data;

// Define a predicate for when the event loop is locked
predicate eloop_locked(struct eloop *e, void *handler, void *data) =
    malloc_block_eloop(e) &*&
    locked(&e->lock, eloop_inv(e, handler, data)) &*&
    e->signalCount |-> ?count &*&
    e->handler |-> handler &*&
    e->handlerData |-> data;
@*/

// Create a new event loop
struct eloop *eloop_create(eloop_handler *handler, void *data)
    //@ requires eloop_handler_data(handler)(data);
    //@ ensures result == 0 ? eloop_handler_data(handler)(data) : eloop(result, handler, data);
{
    struct eloop *e = malloc(sizeof(struct eloop));
    if (e == 0) return 0;
    
    e->signalCount = 0;
    e->handler = handler;
    e->handlerData = data;
    
    //@ close eloop_inv(e, handler, data)();
    init(&e->lock);
    
    //@ close eloop(e, handler, data);
    return e;
}

// Signal the event loop
void eloop_signal(struct eloop *e)
    //@ requires [?f]eloop(e, ?handler, ?data);
    //@ ensures [f]eloop(e, handler, data);
{
    //@ open [f]eloop(e, handler, data);
    acquire(&e->lock);
    //@ open eloop_inv(e, handler, data)();
    
    e->signalCount++;
    
    if (e->signalCount == 1) {
        eloop_handler *h = e->handler;
        void *d = e->handlerData;
        
        //@ close eloop_inv(e, handler, data)();
        release(&e->lock);
        
        h(d);
        
        acquire(&e->lock);
        //@ open eloop_inv(e, handler, data)();
        e->signalCount--;
        //@ close eloop_inv(e, handler, data)();
        release(&e->lock);
    } else {
        //@ close eloop_inv(e, handler, data)();
        release(&e->lock);
    }
    
    //@ close [f]eloop(e, handler, data);
}

// Destroy the event loop
void eloop_destroy(struct eloop *e)
    //@ requires eloop(e, ?handler, ?data);
    //@ ensures eloop_handler_data(handler)(data);
{
    //@ open eloop(e, handler, data);
    acquire(&e->lock);
    //@ open eloop_inv(e, handler, data)();
    
    // Get the handler data
    void *d = e->handlerData;
    eloop_handler *h = e->handler;
    
    // Finalize the lock
    finalize(&e->lock);
    
    // Free the event loop
    free(e);
    
    //@ close eloop_handler_data(h)(d);
}