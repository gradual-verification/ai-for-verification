// Example from Kasper Svendsen and Lars Birkedal, Impredicative Concurrent Abstract Predicates, ESOP 2014.

#include <stdlib.h>
#include "gotsmanlock.h"


typedef struct eloop *eloop;

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


// TODO: make this function pass the verification
typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);
    
/*@
// Add the predicate to verify that a function is an eloop_handler
predicate is_eloop_handler(eloop_handler *h, eloop x, predicate(void *) dataPred) =
    is_eloop_handler_function_pointer(h) == true &*&
    h != 0 &*&
    handler_for(h) == pair(x, dataPred);

// Helper function to associate a handler with its eloop and dataPred
fixpoint pair<eloop, predicate(void *)> handler_for(eloop_handler *h);
@*/