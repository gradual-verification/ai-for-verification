// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"

typedef struct eloop *eloop;

typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);

struct eloop {
    int lock;
    int signalCount;
    eloop_handler *handler;
    //@ predicate(void *) dataPred;
    void *handlerData;
};

/*@

predicate_ctor I(eloop x)() =
    x->signalCount |-> ?signalCount &*& 0 <= signalCount &*&
    x->handler |-> ?h &*&
    x->dataPred |-> ?dataPred &*&
    h == 0 ?
        x->handlerData |-> _ &*&
        true
    :
        x->handlerData |-> ?data &*&
        [_]is_eloop_handler(h, x, dataPred) &*& [_]dataPred(data);

predicate eloop(eloop x) =
    [_]lock(&x->lock, I(x));
@*/

// Example usage of eloop_handler
void example_handler(void *data)
    //@ requires eloop(?x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);
{
    // Handler logic here
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct eloop *loop = malloc(sizeof(struct eloop));
    if (loop == 0) abort();
    loop->signalCount = 0;
    loop->handler = example_handler;
    //@ close I(loop)();
    //@ close exists<I(loop)>();
    init(&loop->lock);
    //@ close eloop(loop);

    // Use the handler
    example_handler(loop->handlerData);

    // Clean up
    finalize(&loop->lock);
    free(loop);
    return 0;
}