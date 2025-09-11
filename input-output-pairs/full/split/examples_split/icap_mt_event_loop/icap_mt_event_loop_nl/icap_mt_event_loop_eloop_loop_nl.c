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


// TODO: make this function pass the verification
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

