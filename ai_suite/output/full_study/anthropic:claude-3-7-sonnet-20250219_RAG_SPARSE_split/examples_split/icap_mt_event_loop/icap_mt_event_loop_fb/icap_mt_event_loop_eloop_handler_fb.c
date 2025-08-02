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
// Helper lemma to open and close the eloop predicate
lemma void open_close_eloop(eloop x)
    requires eloop(x);
    ensures eloop(x);
{
    open eloop(x);
    close eloop(x);
}

// Helper lemma to open and close the lock invariant
lemma void open_close_lock_invariant(eloop x)
    requires [?f]lock(&x->lock, I(x));
    ensures [f]lock(&x->lock, I(x));
{
    open [f]lock(&x->lock, I(x));
    close [f]lock(&x->lock, I(x));
}
@*/