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
// Define a predicate for the event loop invariant
predicate_ctor eloop_inv(eloop x, predicate() P)() = 
    x->signalCount |-> ?count &*& 
    x->handler |-> ?handler &*& 
    x->handlerData |-> ?data &*& 
    P();

// Define a predicate for the event loop
predicate eloop(eloop x, predicate() P) = 
    x != 0 &*& 
    malloc_block_eloop(x) &*& 
    [?f]lock(&x->lock, eloop_inv(x, P));
@*/

/***
 * Description:
The eloop_signal function increments the signal of the given event loop instance.
It makes sure that the property of that event loop is unchanged.

@param x: the event loop instance.
*/
void eloop_signal(eloop x)
//@ requires eloop(x, ?P);
//@ ensures eloop(x, P);
{
    //@ open eloop(x, P);
    acquire(&x->lock);
    //@ open eloop_inv(x, P)();
    if (x->signalCount == INT_MAX) abort();
    x->signalCount++;
    //@ close eloop_inv(x, P)();
    release(&x->lock);
    //@ close eloop(x, P);
}