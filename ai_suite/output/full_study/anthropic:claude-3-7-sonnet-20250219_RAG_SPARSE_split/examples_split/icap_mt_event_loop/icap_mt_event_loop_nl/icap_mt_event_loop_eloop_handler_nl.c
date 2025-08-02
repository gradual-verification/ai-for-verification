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


/*@
// Define a predicate for the data that the handler will operate on
predicate handler_data(void *data;);

// Define a predicate for the event loop
predicate eloop_p(eloop e;) = 
    e != 0 &*&
    e->lock |-> ?l &*&
    e->signalCount |-> ?count &*&
    e->handler |-> ?h &*&
    e->handlerData |-> ?hdata &*&
    malloc_block_eloop(e);

// Define a predicate for the lock invariant
predicate_ctor eloop_inv(eloop e)() =
    e->signalCount |-> ?count &*&
    e->handler |-> ?h &*&
    e->handlerData |-> ?hdata &*&
    handler_data(hdata);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The eloop_handler function pointer that handles the data of an event loop and preserves the property of event loop and data.

@param data: the data to be handled, which needs to preserve some property before and after the execution of handler.
*/
typedef void eloop_handler(void *data);
//@ requires handler_data(data);
//@ ensures handler_data(data);