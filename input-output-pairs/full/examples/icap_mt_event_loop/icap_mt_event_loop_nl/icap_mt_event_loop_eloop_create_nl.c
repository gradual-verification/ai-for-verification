// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


// TODO: make this function pass the verification
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

