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


bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foreach(?fvs, foo) &*& f2->value |-> ?value &*& mem(pair(f1, assoc(fvs, f1)), fvs) == true;
    //@ ensures foreach(fvs, foo) &*& f2->value |-> value &*& result == (assoc(fvs, f1) == value);
{
    //@ open foreach(fvs, foo);
    //@ if (fvs == nil) { assert false; }
    //@ assert fvs == cons(?fv, ?fvs0);
    //@ if (fst(fv) == f1) {
    //@     open foo(fv);
    //@ } else {
    //@     assert foreach(fvs0, foo);
    //@     assert mem(pair(f1, assoc(fvs, f1)), fvs0);
    //@     assert assoc(fvs, f1) == assoc(fvs0, f1);
    //@ }
    //@ open foo(pair(f1, assoc(fvs, f1)));
    int f1_value = f1->value;
    //@ close foo(pair(f1, assoc(fvs, f1)));
    
    //@ if (fst(fv) == f1) {
    //@     close foo(fv);
    //@ } else {
    //@     close foreach(fvs0, foo);
    //@ }
    //@ close foreach(fvs, foo);
    
    return f1_value == f2->value;
}