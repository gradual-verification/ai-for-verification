// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;

// C-level forward declaration of the handler type.
typedef void eloop_handler(void *data);

/*@
// A predicate family to specify the invariant of the data handled by an eloop_handler.
// It is indexed by the handler function pointer.
predicate_family eloop_handler_inv(eloop_handler *h)(void *data);
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
// VeriFast-level contract for the handler type.
// This is merged with the C typedef.
/*@
typedef void eloop_handler(void *data);
    requires eloop_handler_inv(this)(data);
    ensures eloop_handler_inv(this)(data);
@*/

/*@
// The lock invariant for an event loop.
// It protects the signalCount, the handler/data pair, and the struct's memory block.
predicate_ctor eloop_inv(eloop x)() =
    malloc_block_eloop(x) &*&
    x->signalCount |-> ?sc &*& sc <= INT_MAX &*&
    x->handler |-> ?h &*&
    x->handlerData |-> ?d &*&
    is_eloop_handler(h) == true &*&
    eloop_handler_inv(h)(d);

// The predicate representing ownership of an event loop.
// It includes a fractional permission to the lock.
predicate eloop_pred(eloop x) =
    x != 0 &*&
    [1/2]lock(&x->lock, eloop_inv(x));
@*/


// TODO: make this function pass the verification
/***
 * Description:
The eloop_signal function increments the signal of the given event loop instance.
It makes sure that the property of that event loop is unchanged.

@param x: the event loop instance.
*/
void eloop_signal(eloop x)
    //@ requires eloop_pred(x);
    //@ ensures eloop_pred(x);
{
    //@ open eloop_pred(x);
    acquire(&x->lock);
    //@ open eloop_inv(x)();
    if (x->signalCount == INT_MAX) abort();
    x->signalCount++;
    //@ close eloop_inv(x)();
    release(&x->lock);
    //@ close eloop_pred(x);
}