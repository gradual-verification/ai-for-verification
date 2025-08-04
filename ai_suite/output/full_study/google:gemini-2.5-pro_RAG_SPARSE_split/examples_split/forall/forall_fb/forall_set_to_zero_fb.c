#include "prelude.h"

/*@
lemma void take_update_one_decomp<t>(int k, t v, list<t> l)
    requires 0 <= k &*& k < length(l);
    ensures take(k + 1, update(k, v, l)) == append(take(k, l), cons(v, nil));
{
    switch(l) {
        case nil:
        case cons(h, t):
            if (k == 0) {
            } else {
                take_update_one_decomp(k - 1, v, t);
            }
    }
}

lemma void all_eq_append<t>(list<t> xs, list<t> ys, t v)
    requires all_eq(xs, v) == true &*& all_eq(ys, v) == true;
    ensures all_eq(append(xs, ys), v) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            all_eq_append(t, ys, v);
    }
}

lemma void drop_update_unrelated<t>(int i, int j, t v, list<t> xs)
    requires 0 <= j &*& j < i &*& i <= length(xs);
    ensures drop(i, update(j, v, xs)) == drop(i, xs);
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (i > 0) {
                if (j == 0) {
                    // Update is on head, but we drop it, so the rest is the same.
                } else {
                    drop_update_unrelated(i - 1, j - 1, v, t);
                }
            }
    }
}
@*/

// TODO: make this function pass the verification
void set_to_zero(int* a, int N) 
  //@ requires a[0..N] |-> ?vs;
  //@ ensures a[0..N] |-> ?nvs &*& forall_(int i; i < 0 || i >= length(vs) || nth(i, nvs) == 0);
{
  int k = 0;
  while(k < N) 
    //@ invariant 0 <= k &*& k <= N &*& a[0..N] |-> ?current_vs &*& all_eq(take(k, current_vs), 0) == true &*& drop(k, current_vs) == drop(k, vs);
  {
    //@ list<int> old_current_vs = current_vs;
    a[k] = 0;
    
    // The following lemma calls help VeriFast prove that the invariant holds for the next iteration.
    
    // Prove the `all_eq` part of the invariant.
    //@ take_update_one_decomp(k, 0, old_current_vs);
    //@ all_eq_append(take(k, old_current_vs), cons(0, nil), 0);
    
    // Prove the `drop` part of the invariant.
    //@ drop_update_unrelated(k + 1, k, 0, old_current_vs);
    //@ drop_n_plus_one(k, old_current_vs);
    //@ drop_n_plus_one(k, vs);
    
    k++;
  }
}