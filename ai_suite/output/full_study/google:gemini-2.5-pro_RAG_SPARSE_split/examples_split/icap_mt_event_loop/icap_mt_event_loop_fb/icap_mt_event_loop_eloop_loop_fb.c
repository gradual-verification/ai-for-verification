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

// A ghost predicate family to track if we are dispatching a handler.
// This allows us to temporarily move the data predicate out of the lock's invariant.
predicate_family eloop_dispatching(eloop x)(bool isDispatching);

predicate_ctor I_content(eloop x, bool isDispatching) =
    x->signalCount |-> ?signalCount &*& 0 <= signalCount &*&
    x->handler |-> ?h &*&
    x->dataPred |-> ?dataPred &*&
    x->handlerData |-> ?data &*&
    (isDispatching ?
        // When dispatching, the data predicate is held by the thread, not the lock.
        h != 0 &*& [_]is_eloop_handler(h, x, dataPred)
    :
        // When idle, the data predicate is protected by the lock.
        h == 0 ?
            true
        :
            [_]is_eloop_handler(h, x, dataPred) &*& [_]dataPred(data)
    );

predicate_ctor I(eloop x)() =
    eloop_dispatching(x)(?isDispatching) &*& I_content(x, isDispatching);

predicate eloop(eloop x) =
    // The eloop predicate owns the lock and the dispatching state.
    // If dispatching, it also owns the checked-out data predicate.
    [_]lock(&x->lock, I(x)) &*&
    (
        eloop_dispatching(x)(true) ?
            x->handler |-> ?h &*& x->dataPred |-> ?dp &*& x->handlerData |-> ?d &*& [_]dp(d)
        :
            eloop_dispatching(x)(false)
    );
@*/


typedef void eloop_handler/*@(eloop x, predicate(void *) dataPred)@*/(void *data);
    //@ requires eloop(x) &*& [_]dataPred(data);
    //@ ensures eloop(x) &*& [_]dataPred(data);



// TODO: make this function pass the verification
void eloop_loop(eloop x)
    //@ requires eloop(x);
    //@ ensures false;
{
    for (;;)
        //@ invariant eloop(x);
    {
        eloop_handler *handler = 0;
        void *handlerData;
        
        //@ open eloop(x);
        //@ open eloop_dispatching(x)(false);
        acquire(&x->lock);
        //@ open I(x)();
        //@ open I_content(x, false);
        
        if (x->signalCount > 0) {
            x->signalCount--;
            handler = x->handler;
            if (handler) {
                handlerData = x->handlerData;
                //@ close I_content(x, true);
                //@ eloop_dispatching(x)(true);
            } else {
                //@ close I_content(x, false);
                //@ eloop_dispatching(x)(false);
            }
        } else {
            //@ close I_content(x, false);
            //@ eloop_dispatching(x)(false);
        }
        
        //@ close I(x)();
        release(&x->lock);
        
        if (handler) {
            //@ close eloop(x);
            handler(handlerData);
            //@ open eloop(x);
            //@ open eloop_dispatching(x)(true);
            acquire(&x->lock);
            //@ open I(x)();
            //@ open I_content(x, true);
            //@ close I_content(x, false);
            //@ eloop_dispatching(x)(false);
            //@ close I(x)();
            release(&x->lock);
        }
        //@ close eloop(x);
    }
}
