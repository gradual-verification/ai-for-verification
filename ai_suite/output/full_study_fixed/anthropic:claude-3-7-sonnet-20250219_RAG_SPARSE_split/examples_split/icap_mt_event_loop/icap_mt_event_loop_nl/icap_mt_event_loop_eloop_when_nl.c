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
// Predicate to represent the event loop's data property
predicate eloop_data(void *data, eloop_handler *handler);

// Lock invariant for the event loop
predicate_ctor eloop_inv(struct eloop *x)() = 
    x->signalCount |-> ?count &*&
    x->handler |-> ?h &*&
    x->handlerData |-> ?data &*&
    malloc_block_eloop(x) &*&
    (h == 0 ? true : eloop_data(data, h));
@*/

// TODO: make this function pass the verification
/***
 * Description:
The eloop_when function updates the loop handler and data for an event loop instance.
It makes sure that the event loop property holds before and after the execution. 

@param x: the event loop instance.
@param h: the event loop handler.
@param data: the data of an event loop handler
*/
void eloop_when(eloop x, eloop_handler *h, void *data)
//@ requires x != 0 &*& [?f]lock(&x->lock, eloop_inv(x)) &*& eloop_data(data, h);
//@ ensures [f]lock(&x->lock, eloop_inv(x));
{
    acquire(&x->lock);
    //@ open eloop_inv(x)();
    x->handler = h;
    x->handlerData = data;
    //@ close eloop_inv(x)();
    release(&x->lock);
}