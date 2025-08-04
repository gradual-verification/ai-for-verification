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

// The main resource predicate for an eloop must own the malloc_block for the struct
// to allow for its eventual deallocation. The lock itself is part of the struct,
// and the lock predicate `lock` owns the memory for the lock integer. The lock's
// invariant `I(x)` owns the other fields of the struct.
predicate eloop(eloop x) =
    malloc_block_eloop(x) &*&
    [_]lock(&x->lock, I(x));
@*/


typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);
    


// TODO: make this function pass the verification
eloop eloop_create()
    //@ requires true;
    //@ ensures eloop(result);
{
    eloop x = malloc(sizeof(struct eloop));
    if (x == 0) abort();
    x->handler = 0;
    x->signalCount = 0;
    
    // To initialize the lock, we must provide its invariant.
    //@ close exists(I(x));
    init(&x->lock);
    
    // To release the lock for the first time, we must establish its invariant.
    // The invariant requires ownership of the other fields of the struct.
    //@ close I(x)();
    release(&x->lock);
    
    return x;
}