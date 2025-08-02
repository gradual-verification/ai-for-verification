#include "prelude.h"

//@ predicate atomic_cas_allowed(int* c, int old, int new) = true;

// TODO: make this function pass the verification
int atomic_cas(int* c, int old, int new);
    //@ requires atomic_cas_allowed(c, old, new) &*& integer(c, ?current);
    //@ ensures integer(c, current == old ? new : current) &*& result == current;
{
    int current = *c;
    if (current == old) {
        *c = new;
    }
    return current;
}