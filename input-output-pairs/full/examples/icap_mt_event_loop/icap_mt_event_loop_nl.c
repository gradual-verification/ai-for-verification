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

/***
 * Description:
The eloop_create function creates an instance of event loop, whose lock should be initialized and released (i.e., unlocked).
Moreover, its number of signals should be greater than or equal to 0.

@return: the created instance of event loop.
*/
eloop eloop_create()
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    init(&x->lock);
    release(&x->lock);
    return x;
}

/***
 * Description:
The eloop_loop function runs the given event loop infinitely and makes sure that the property of that event loop is unchanged.
It has a forever loop, and does the following things in the loop: acquiring the lock, getting the handler and data (if the signal count > 0),
releasing the lock and handling the data (if the handler is found.)

@param x: the event loop instance to be run.

It makes sure that x presevees the property of event loop before and after the execution.
*/
void eloop_loop(eloop x)
{
    for (;;)
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        acquire(&x->lock);
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler)
                handlerData = x->handlerData;
        }
        release(&x->lock);
        
        if (handler)
            handler(handlerData);
        
    }
}

/***
 * Description:
The eloop_signal function increments the signal of the given event loop instance.
It makes sure that the property of that event loop is unchanged.

@param x: the event loop instance.
*/
void eloop_signal(eloop x)
{
    acquire(&x->lock);
    if (x->signalCount == INT_MAX) abort();
    x->signalCount++;
    release(&x->lock);
}

/***
 * Description:
The eloop_when function updates the loop handler and data for an event loop instance.
It makes sure that the event loop property holds before and after the execution. 

@param x: the event loop instance.
@param h: the event loop handler.
@param data: the data of an event loop handler
*/
void eloop_when(eloop x, eloop_handler *h, void *data)
{
    acquire(&x->lock);
    x->handler = h;
    x->handlerData = data;
    release(&x->lock);
}