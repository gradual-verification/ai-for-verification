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
    predicate_family eloop_handler_inv(eloop_handler *h)(void *data);

    requires eloop_handler_inv(this)(data);
    ensures eloop_handler_inv(this)(data);
@*/

/*@
predicate_ctor eloop_inv(eloop e)() =
    e->signalCount |-> ?sc &*&
    e->handler |-> ?h &*&
    e->handlerData |-> ?hd &*&
    sc >= 0 &*&
    (h == 0 ?
        true
    :
        is_eloop_handler(h) == true &*& eloop_handler_inv(h)(hd)
    );

predicate eloop_pred(eloop e) =
    malloc_block_eloop(e) &*&
    lock(&e->lock, eloop_inv(e));
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
    //@ ensures eloop_pred(result);
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    //@ chars_to_struct(x);
    x->handler = 0;
    x->signalCount = 0;
    
    //@ close exists(eloop_inv(x));
    init(&x->lock);
    
    //@ close eloop_inv(x)();
    release(&x->lock);
    
    //@ close eloop_pred(x);
    return x;
}