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

//@ predicate eloop_inv(eloop x) = x->signalCount |-> ?count &*& 0 <= count &*& x->handler |-> ?handler &*& x->handlerData |-> ?data &*& lock(&x->lock, eloop_inv(x));

/***
 * Description:
The eloop_signal function increments the signal of the given event loop instance.
It makes sure that the property of that event loop is unchanged.

@param x: the event loop instance.
*/
//@ requires eloop_inv(x);
//@ ensures eloop_inv(x);
void eloop_signal(eloop x)
{
    acquire(&x->lock);
    //@ open eloop_inv(x);
    if (x->signalCount == INT_MAX) abort();
    x->signalCount++;
    //@ close eloop_inv(x);
    release(&x->lock);
}