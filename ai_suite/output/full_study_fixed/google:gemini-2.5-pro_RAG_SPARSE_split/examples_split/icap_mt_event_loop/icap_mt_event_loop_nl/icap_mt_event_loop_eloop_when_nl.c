// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;

/*@

// An abstract predicate representing the property that an event loop handler must satisfy.
// This property is parameterized by the handler function pointer and its data.
typedef predicate eloop_prop(eloop_handler* h, void* data);

predicate_ctor eloop_inv(eloop x, eloop_prop* P)() =
    x->signalCount |-> _ &*&
    x->handler |-> ?h &*&
    x->handlerData |-> ?d &*&
    is_eloop_handler(h) == true &*&
    P(h, d);

predicate eloop_pred(eloop x; eloop_prop* P) =
    malloc_block_eloop(x) &*&
    lock(&x->lock, eloop_inv(x, P));

@*/

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
    //@ requires eloop_pred(x, ?P) &*& is_eloop_handler(h) == true &*& P(h, data);
    //@ ensures eloop_pred(x, P) &*& exists<eloop_handler*>(?old_h) &*& exists<void*>(?old_d) &*& P(old_h, old_d);
{
    //@ open eloop_pred(x, P);
    acquire(&x->lock);
    //@ open eloop_inv(x, P)();
    eloop_handler* old_h = x->handler;
    void* old_d = x->handlerData;
    x->handler = h;
    x->handlerData = data;
    //@ close eloop_inv(x, P)();
    release(&x->lock);
    //@ close eloop_pred(x, P);
}