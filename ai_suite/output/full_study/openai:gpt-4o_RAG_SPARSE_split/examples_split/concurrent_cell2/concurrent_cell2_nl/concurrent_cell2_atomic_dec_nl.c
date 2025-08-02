#include "prelude.h"

//@ predicate atomic_dec_permission(int *c, int v) = integer(c, v);

void atomic_dec(int* c);
    //@ requires atomic_dec_permission(c, ?v) &*& v > 0;
    //@ ensures atomic_dec_permission(c, v - 1);

void atomic_dec(int* c) {
    //@ open atomic_dec_permission(c, ?v);
    //@ integer_limits(c);
    while (true) 
    //@ invariant integer(c, ?cv) &*& cv >= 0;
    {
        int old = *c;
        if (old > 0) {
            if (__sync_bool_compare_and_swap(c, old, old - 1)) {
                //@ close atomic_dec_permission(c, old - 1);
                return;
            }
        } else {
            //@ close atomic_dec_permission(c, old);
            return;
        }
    }
}