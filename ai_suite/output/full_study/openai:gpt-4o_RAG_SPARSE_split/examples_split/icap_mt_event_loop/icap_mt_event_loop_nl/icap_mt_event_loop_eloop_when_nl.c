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

//@ predicate eloop_inv(eloop x, eloop_handler *h, void *data) = 
//@     x->handler |-> h &*& x->handlerData |-> data;

/*@
predicate eloop(eloop x, eloop_handler *h, void *data) =
    x->lock |-> ?lock &*&
    lock(&x->lock, eloop_inv(x, h, data)) &*&
    eloop_inv(x, h, data);
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
//@ requires eloop(x, ?old_h, ?old_data);
//@ ensures eloop(x, h, data);
void eloop_when(eloop x, eloop_handler *h, void *data)
{
    acquire(&x->lock);
    //@ open eloop_inv(x, old_h, old_data);
    x->handler = h;
    x->handlerData = data;
    //@ close eloop_inv(x, h, data);
    release(&x->lock);
}