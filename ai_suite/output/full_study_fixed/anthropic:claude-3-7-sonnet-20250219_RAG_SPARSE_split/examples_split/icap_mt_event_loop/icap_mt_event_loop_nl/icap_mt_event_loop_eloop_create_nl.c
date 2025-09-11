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
// Define a predicate for the event loop
predicate eloop_inv(struct eloop *x, predicate() I) =
    x->signalCount |-> ?count &*& count >= 0 &*&
    x->handler |-> ?handler &*&
    x->handlerData |-> ?data &*&
    malloc_block_eloop(x) &*&
    I();

// Define a predicate for the event loop pointer
predicate eloop(struct eloop *x, predicate() I) =
    lock(&x->lock, eloop_inv(x, I));
@*/

// TODO: make this function pass the verification
/***
 * Description:
The eloop_create function creates an instance of event loop, whose lock should be initialized and released (i.e., unlocked).
Moreover, its number of signals should be greater than or equal to 0.

@return: the created instance of event loop.
*/
eloop eloop_create()
    //@ requires exists<predicate()>(?I) &*& I();
    //@ ensures result == 0 ? I() : eloop(result, I);
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    //@ close eloop_inv(x, I);
    //@ close exists<predicate()>(eloop_inv(x, I));
    init(&x->lock);
    release(&x->lock);
    //@ close eloop(x, I);
    return x;
}