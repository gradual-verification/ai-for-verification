// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"

/*@
// This predicate family represents an abstract property of the data associated with an event loop handler.
// A concrete handler implementation will define a specific instance of this family
// to specify the resources it operates on.
predicate_family eloop_data_property(void *handler)(void *data);
@*/

typedef struct eloop *eloop;

// TODO: make this function pass the verification
/***
 * Description:
The eloop_handler function pointer that handles the data of an event loop and preserves the property of event loop and data.

@param data: the data to be handled, which needs to preserve some property before and after the execution of handler.
*/
typedef void eloop_handler(void *data);
//@ requires eloop_data_property(this)(data);
//@ ensures eloop_data_property(this)(data);


struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    void *handlerData;
};

/*@
// This predicate constructor defines the invariant for the event loop's lock.
// The invariant protects the fields of the `eloop` struct. It ensures that
// there is a valid handler and that the property associated with the handler's data holds.
predicate_ctor eloop_inv(struct eloop *e)() =
    e->signalCount |-> ?sc &*& 0 <= sc &*&
    e->handler |-> ?h &*&
    e->handlerData |-> ?h_data &*&
    is_eloop_handler(h) == true &*&
    eloop_data_property(h)(h_data);

// This predicate represents a complete, valid event loop object.
// It owns the memory for the struct and the lock that protects its fields.
predicate eloop(struct eloop *e) =
    malloc_block_eloop(e) &*&
    lock(&e->lock, eloop_inv(e));
@*/