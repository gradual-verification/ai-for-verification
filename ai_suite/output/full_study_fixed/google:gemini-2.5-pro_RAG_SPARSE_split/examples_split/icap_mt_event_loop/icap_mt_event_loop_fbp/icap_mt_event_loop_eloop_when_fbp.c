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
    eloop_dataPred(x, ?dataPred) &*&
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
void eloop_when(eloop x, eloop_handler *h, void *data)
    //@ requires eloop(x) &*& h == 0 ? true : [_]is_eloop_handler(h, x, ?dataPred) &*& [_]dataPred(data);
    //@ ensures eloop(x);
{
    acquire(&x->lock);
    //@ open I(x)();
    //@ assert x->signalCount |-> _ &*& x->handler |-> ?old_h &*& eloop_dataPred(x, ?old_dp) &*& x->handlerData |-> ?old_data;
    
    /*@
    if (old_h != 0) {
        // The old handler's resources are no longer needed inside the lock.
        // Since they are fractional, we can leak them.
        leak [_]is_eloop_handler(old_h, x, old_dp) &*& [_]old_dp(old_data);
    }
    @*/
    
    x->handler = h;
    x->handlerData = data;
    
    if (h != 0) {
        // Update the ghost field to store the data predicate for the new handler.
        //@ open eloop_dataPred(x, old_dp);
        //@ close eloop_dataPred(x, dataPred);
    }
    
    //@ close I(x)();
    release(&x->lock);
}
