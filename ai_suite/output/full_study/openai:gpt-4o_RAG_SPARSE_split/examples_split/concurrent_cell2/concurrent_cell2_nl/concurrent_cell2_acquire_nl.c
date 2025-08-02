#include "prelude.h"

// Specification for atomic_cas
/*@
predicate atomic_cas_allowed(int *c);

predicate lock_acquired(int *c);

fixpoint bool is_locked(int v) { return v == 1; }

fixpoint bool is_unlocked(int v) { return v == 0; }

lemma void atomic_cas_preserves_lock(int *c, int old, int new);
    requires atomic_cas_allowed(c) &*& is_unlocked(old) &*& is_locked(new);
    ensures atomic_cas_allowed(c) &*& (old == 0 ? lock_acquired(c) : true);

@*/

// atomic_cas function
/*@
requires atomic_cas_allowed(c);
ensures atomic_cas_allowed(c) &*& (result == old ? (old == 0 ? lock_acquired(c) : true) : true);
@*/
int atomic_cas(int* c, int old, int new);

// acquire function
// TODO: make this function pass the verification
/*@
requires atomic_cas_allowed(c);
ensures lock_acquired(c);
@*/
void acquire(int* c)
{
  while(true)
  //@ invariant atomic_cas_allowed(c);
  {
    int read = atomic_cas(c, 0, 1);
    if(read == 0) {
      //@ assert lock_acquired(c);
      break;
    }
  }
}