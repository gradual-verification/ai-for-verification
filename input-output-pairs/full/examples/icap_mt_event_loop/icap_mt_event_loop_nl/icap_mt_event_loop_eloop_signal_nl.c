// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


// TODO: make this function pass the verification
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

