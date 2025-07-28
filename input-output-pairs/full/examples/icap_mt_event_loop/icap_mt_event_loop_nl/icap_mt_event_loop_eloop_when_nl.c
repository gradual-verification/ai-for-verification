// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


// TODO: make this function pass the verification
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