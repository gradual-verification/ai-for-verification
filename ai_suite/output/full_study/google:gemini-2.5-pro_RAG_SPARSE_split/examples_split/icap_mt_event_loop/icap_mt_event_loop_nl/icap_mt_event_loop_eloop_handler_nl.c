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
// A data_predicate is an abstract predicate on the handler's data.
// The handler must preserve this predicate.
typedef predicate data_predicate(void *data);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The eloop_handler function pointer that handles the data of an event loop and preserves the property of event loop and data.

@param data: the data to be handled, which needs to preserve some property before and after the execution of handler.
*/
typedef void eloop_handler(void *data);
//@ requires exists<data_predicate *>(?P) &*& P(data);
//@ ensures P(data);
