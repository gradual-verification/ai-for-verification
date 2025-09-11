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
    

// TODO: make this function pass the verification
void eloop_loop(eloop x)
    //@ requires eloop(x);
    //@ ensures false;
{
    for (;;)
        //@ invariant eloop(x);
    {
        eloop_handler *handler_to_call = 0;
        void *data_to_call;
        //@ predicate(void *) dp_to_call;

        acquire(&x->lock);
        //@ open I(x)();
        if (x->signalCount > 0) {
            x->signalCount--;
            handler_to_call = x->handler;
            if (handler_to_call) {
                data_to_call = x->handlerData;
                //@ dp_to_call = x->dataPred;
                // Temporarily remove handler from the invariant to take its permissions out.
                x->handler = 0;
            }
        }
        //@ close I(x)();
        release(&x->lock);
        
        if (handler_to_call) {
            //@ open [_]is_eloop_handler(handler_to_call, x, dp_to_call);
            handler_to_call(data_to_call);
            
            // Restore the handler in a second critical section.
            acquire(&x->lock);
            //@ open I(x)();
            x->handler = handler_to_call;
            //@ close I(x)();
            release(&x->lock);
        }
    }
}