#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

/*@

predicate map(struct node *n; list<pair<void *, void *> > entries) =
    n == 0 ?
        entries == nil
    :
        n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value &*&
        map(next, ?entriesTail) &*& entries == cons(pair(key, value), entriesTail);

@*/

/*@
fixpoint bool contains<t>(list<t> xs, t x) {
    switch (xs) {
        case nil: return false;
        case cons(x0, xs0): return x0 == x || contains(xs0, x);
    }
}

fixpoint bool is_suffix_of<t>(list<t> xs, list<t> ys) {
    switch (ys) {
        case nil: return xs == ys;
        case cons(y, ys0): return xs == ys || is_suffix_of(xs, ys0);
    }
}
@*/

struct foo {
    int value;
};

/*@

predicate foo(pair<struct foo *, int> fv;) =
    switch (fv) {
        case pair(f, v): return f->value |-> v;
    };

fixpoint b assoc<a, b>(list<pair<a, b> > xys, a x) {
    switch (xys) {
        case nil: return default_value;
        case cons(xy, xys0): return fst(xy) == x ? snd(xy) : assoc(xys0, x);
    }
}

@*/

/*@

// Helper fixpoints and lemmas for the example implementation.
// These are often found in VeriFast's listex.gh library.

fixpoint list<t> filter<t>(fixpoint(t, bool) p, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return p(x) ? cons(x, filter(p, xs0)) : filter(p, xs0);
    }
}

fixpoint bool is_eq<t>(t y, t x) { return x == y; }

lemma void contains_filter<t>(fixpoint(t, bool) p, list<t> xs, t x)
    requires true;
    ensures contains(filter(p, xs), x) == (mem(x, xs) && p(x));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (h == x) {
            } else {
                contains_filter(p, t, x);
            }
    }
}

predicate_family equals_data(void *funcp)(list<void *> keys, void *key00, list<void *> eqKeys, predicate() p);

predicate_family_instance equals_data(pointer_equals)(list<void *> keys, void *key00, list<void *> eqKeys, predicate() p) =
    eqKeys == filter((is_eq)(key00), keys) &*& p == emp;

@*/

// The original typedef is unimplementable by any C function, as the implementation cannot
// depend on the ghost parameter 'eqKeys'. The standard VeriFast pattern to make such a generic
// function pointer type implementable is to use a predicate family to associate ghost state
// with each specific function pointer.
// We also provide an example implementation 'pointer_equals' to demonstrate its use.
typedef bool equalsFuncType(void *key, void *key0);
    //@ requires equals_data(this)(?keys, ?key00, ?eqKeys, ?p) &*& p() &*& mem(key, keys) == true &*& key0 == key00;
    //@ ensures equals_data(this)(keys, key00, eqKeys, p) &*& p() &*& result == contains(eqKeys, key);

// An example function that implements the function type for pointer equality.
bool pointer_equals(void *key, void *key0) //@ : equalsFuncType
    //@ requires equals_data(pointer_equals)(?keys, ?key00, ?eqKeys, ?p) &*& p() &*& mem(key, keys) == true &*& key0 == key00;
    //@ ensures equals_data(pointer_equals)(keys, key00, eqKeys, p) &*& p() &*& result == (key == key0);
{
    //@ open equals_data(pointer_equals)(keys, key00, eqKeys, p);
    //@ contains_filter((is_eq)(key00), keys, key);
    return key == key0;
}
