#include "prelude.h"

/*@
// Lemma: all_eq distributes over append.
lemma void all_eq_append<t>(list<t> xs, list<t> ys, t val)
    requires all_eq(xs, val) == true &*& all_eq(ys, val) == true;
    ensures all_eq(append(xs, ys), val) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            all_eq_append(t, ys, val);
    }
}

// Lemma: Shows that updating an element preserves the all_eq property of the prefix.
lemma void take_update_all_eq<t>(int k, t val, list<t> xs)
    requires 0 <= k &*& k < length(xs) &*& all_eq(take(k, xs), val) == true;
    ensures all_eq(take(k + 1, update(k, val, xs)), val) == true;
{
    list<t> updated_xs = update(k, val, xs);
    
    // Prove take(k + 1, update(k, val, xs)) == append(take(k, xs), cons(val, nil))
    assert take(k, updated_xs) == take(k, xs);
    assert nth(k, updated_xs) == val;
    append_take_drop_n(updated_xs, k + 1);
    drop_n_plus_one(k, updated_xs);
    assert take(k + 1, updated_xs) == append(take(k, updated_xs), cons(nth(k, updated_xs), nil));
    assert take(k + 1, updated_xs) == append(take(k, xs), cons(val, nil));

    // Prove all_eq(append(take(k, xs), cons(val, nil)), val)
    all_eq_append(take(k, xs), cons(val, nil), val);
}

// Lemma: Shows that updating an element does not affect the suffix of another list if their suffixes were already equal.
lemma void drop_update_eq<t>(int k, t val, list<t> xs, list<t> ys)
    requires 0 <= k &*& k < length(xs) &*& drop(k, xs) == drop(k, ys);
    ensures drop(k + 1, update(k, val, xs)) == drop(k + 1, ys);
{
    list<t> updated_xs = update(k, val, xs);
    assert drop(k + 1, updated_xs) == drop(k + 1, xs);
    
    length_drop(k, xs);
    length_drop(k, ys);
    assert length(xs) == length(ys);
    assert k < length(ys);
    
    drop_n_plus_one(k, xs);
    drop_n_plus_one(k, ys);
    
    assert tail(drop(k, xs)) == tail(drop(k, ys));
    assert drop(k + 1, xs) == drop(k + 1, ys);
}

// Lemma: Converts an all_eq property to a forall_ property.
lemma void all_eq_to_forall_nth_eq<t>(list<t> xs, t val)
    requires all_eq(xs, val) == true;
    ensures forall_(int i; i < 0 || i >= length(xs) || nth(i, xs) == val);
{
    forall_t_elim(all_values<int>, (λ(int i) { i < 0 || i >= length(xs) || nth(i, xs) == val }), ?i);
    if (i >= 0 && i < length(xs)) {
        all_eq_nth(xs, val, i);
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
    /*@
    invariant 0 <= k &*& k <= N &*&
                a[0..N] |-> ?current_vs &*&
                length(current_vs) == N &*&
                all_eq(take(k, current_vs), 0) == true &*&
                drop(k, current_vs) == drop(k, vs);
    @*/
  {
    //@ list<int> old_current_vs = current_vs;
    a[k] = 0;
    
    //@ take_update_all_eq(k, 0, old_current_vs);
    //@ drop_update_eq(k, 0, old_current_vs, vs);
    
    k++;
  }
  
  //@ assert a[0..N] |-> ?nvs;
  //@ assert length(vs) == N;
  //@ take_length(nvs);
  //@ all_eq_to_forall_nth_eq(nvs, 0);
}