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
predicate eloop(struct eloop *e, predicate() I) =
    e->handler |-> _ &*&
    e->handlerData |-> _ &*&
    e->signalCount |-> 0 &*&
    lock(&e->lock, I) &*&
    malloc_block_eloop(e);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The eloop_create function creates an instance of event loop, whose lock should be initialized and released (i.e., unlocked).
Moreover, its number of signals should be greater than or equal to 0.

@return: the created instance of event loop.
*/
/*@
requires exists<predicate()>(?I);
ensures result == 0 ? true : eloop(result, I);
@*/
eloop eloop_create()
{
    struct eloop *x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    //@ close exists(I);
    init(&x->lock);
    //@ close eloop(x, I);
    release(&x->lock);
    return x;
}