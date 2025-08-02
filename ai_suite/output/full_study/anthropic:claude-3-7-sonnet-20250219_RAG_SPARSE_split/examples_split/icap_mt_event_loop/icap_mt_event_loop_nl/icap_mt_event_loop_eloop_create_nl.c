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
// Define a predicate for the event loop
predicate eloop(struct eloop *x; int signalCount, eloop_handler *handler, void *handlerData) =
    x != 0 &*&
    x->signalCount |-> signalCount &*&
    x->handler |-> handler &*&
    x->handlerData |-> handlerData &*&
    signalCount >= 0 &*&
    lock(&x->lock, ?I) &*&
    malloc_block_eloop(x);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The eloop_create function creates an instance of event loop, whose lock should be initialized and released (i.e., unlocked).
Moreover, its number of signals should be greater than or equal to 0.

@return: the created instance of event loop.
*/
eloop eloop_create()
//@ requires true;
//@ ensures result == 0 ? true : eloop(result, 0, 0, 0);
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    //@ close exists<predicate()>(?I);
    init(&x->lock);
    release(&x->lock);
    //@ close eloop(x, 0, 0, 0);
    return x;
}