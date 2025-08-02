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

//@ predicate eloop_predicate(eloop e) = e->handler |-> _ &*& e->signalCount |-> 0 &*& e->handlerData |-> _;

/***
 * Description:
The eloop_create function creates an instance of event loop, whose lock should be initialized and released (i.e., unlocked).
Moreover, its number of signals should be greater than or equal to 0.

@return: the created instance of event loop.
*/
//@ requires true;
//@ ensures result == 0 ? true : eloop_predicate(result) &*& lock(&result->lock, eloop_predicate(result));

eloop eloop_create()
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    //@ close exists(eloop_predicate(x));
    init(&x->lock);
    //@ close eloop_predicate(x);
    release(&x->lock);
    return x;
}