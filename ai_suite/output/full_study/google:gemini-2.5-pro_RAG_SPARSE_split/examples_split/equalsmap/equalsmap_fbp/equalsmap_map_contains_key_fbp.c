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
        n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value &*& malloc_block_node(n) &*&
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

lemma void is_suffix_of_mem<t>(list<t> xs, list<t> ys)
    requires xs != nil &*& is_suffix_of(xs, ys) == true;
    ensures mem(head(xs), ys) == true;
{
    switch (ys) {
        case nil:
        case cons(y, ys0):
            if (xs == ys) {
            } else {
                is_suffix_of_mem(xs, ys0);
            }
    }
}

lemma void is_suffix_of_tail<t>(list<t> xs, list<t> l)
    requires xs != nil &*& is_suffix_of(xs, l) == true;
    ensures is_suffix_of(tail(xs), l) == true;
{
    switch(l) {
        case nil:
        case cons(h, t):
            if (xs == l) {
            } else {
                is_suffix_of_tail(xs, t);
            }
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


typedef bool equalsFuncType/*@ (list<void *> keys, void *key00, list<void *> eqKeys, predicate() p) @*/(void *key, void *key0);
    //@ requires p() &*& mem(key, keys) == true &*& key0 == key00;
    //@ ensures p() &*& result == contains(eqKeys, key);



// TODO: make this function pass the verification
bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires [_]is_equalsFuncType(equalsFunc, ?keys, key, ?eqKeys, ?p) &*& p() &*& map(map, ?entries) &*& is_suffix_of(map((fst), entries), keys) == true;
    //@ ensures p() &*& map(map, entries) &*& result == exists(map((fst), entries), (contains)(eqKeys));
{
    open map(map, entries);
    if (map == 0) {
        close map(0, nil);
        return false;
    } else {
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            close map(map, entries);
            return true;
        } else {
            bool rec_result = map_contains_key(map->next, key, equalsFunc);
            close map(map, entries);
            return rec_result;
        }
    }
}