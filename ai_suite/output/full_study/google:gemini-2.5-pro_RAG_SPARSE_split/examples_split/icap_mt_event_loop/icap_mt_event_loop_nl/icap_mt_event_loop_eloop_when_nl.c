    //@ requires eloop_handler_data(this)(data, ?P) &*& P();
    //@ ensures P();
// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;

// Forward declaration for use in predicates and struct definitions.
struct eloop;
typedef void eloop_handler(void *data);

/*@
// This predicate family associates a handler function and its data with an abstract
// property `P` that it must preserve.
predicate_family eloop_handler_data(eloop_handler* h)(void* data, predicate() P);

// This is the invariant protected by the lock inside the event loop.
// It owns the fields of the struct that are mutable and shared.
predicate_ctor eloop_inv(eloop x, predicate() P)() =
    x->signalCount |-> _ &*&
    x->handler |-> ?h &*&
    is_eloop_handler(h) == true &*&
    x->handlerData |-> ?d &*&
    eloop_handler_data(h)(d, P);

// This predicate represents a valid event loop instance `x` that maintains
// the abstract property `P`.
predicate eloop(eloop x; predicate() P) =
    malloc_block_eloop(x) &*&
    lock(&x->lock, eloop_inv(x, P));
@*/

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
    //@ requires eloop_handler_data(this)(data, ?P) &*& P();
    //@ ensures P();


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
    /*@
    requires
        [?f]eloop(x, ?P) &*&
        is_eloop_handler(h) == true &*&
        eloop_handler_data(h)(data, P);
    @*/
    /*@
    ensures
        [f]eloop(x, P) &*&
        is_eloop_handler(?old_h) == true &*&
        eloop_handler_data(old_h)(?old_data, P);
    @*/
{
    //@ open eloop(x, P);
    acquire(&x->lock);
    //@ open eloop_inv(x, P)();
    x->handler = h;
    x->handlerData = data;
    //@ close eloop_inv(x, P)();
    release(&x->lock);
    //@ close [f]eloop(x, P);
}