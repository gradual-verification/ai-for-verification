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
// Define a predicate for the invariant of the lock
predicate_ctor eloop_inv(struct eloop *x)() = 
    x->signalCount |-> ?count &*& 
    x->handler |-> ?handler &*& 
    x->handlerData |-> ?data &*&
    count >= 0 &*& count <= INT_MAX;

// Define a predicate for the eloop structure
predicate eloop(struct eloop *x) = 
    malloc_block_eloop(x) &*& 
    lock(&x->lock, eloop_inv(x));
@*/

/***
 * Description:
The eloop_signal function increments the signal of the given event loop instance.
It makes sure that the property of that event loop is unchanged.

@param x: the event loop instance.
*/
void eloop_signal(eloop x)
//@ requires eloop(x);
//@ ensures eloop(x);
{
    acquire(&x->lock);
    //@ open eloop_inv(x)();
    if (x->signalCount == INT_MAX) abort();
    x->signalCount++;
    //@ close eloop_inv(x)();
    release(&x->lock);
}