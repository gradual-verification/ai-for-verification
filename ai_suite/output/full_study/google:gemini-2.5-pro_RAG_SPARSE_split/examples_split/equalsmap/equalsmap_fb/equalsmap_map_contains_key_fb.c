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

lemma void suffix_of_tail<t>(list<t> t, t h, list<t> ys)
    requires is_suffix_of(cons(h, t), ys) == true;
    ensures is_suffix_of(t, ys) == true;
{
    switch (ys) {
        case nil:
        case cons(y, ys0):
            if (cons(h, t) == ys) {
                // is_suffix_of(t, cons(h, t)) holds by definition.
            } else {
                // is_suffix_of(cons(h, t), ys0) holds.
                suffix_of_tail(t, h, ys0); // Apply induction.
                // is_suffix_of(t, ys0) holds.
                // is_suffix_of(t, ys) is (t == ys || is_suffix_of(t, ys0)), which is true.
            }
    }
}

lemma void is_suffix_of_head_mem<t>(list<t> xs, list<t> ys)
    requires is_suffix_of(xs, ys) == true &*& xs != nil;
    ensures mem(head(xs), ys) == true;
{
    switch (ys) {
        case nil: // xs must be nil, which contradicts xs != nil.
        case cons(y, ys0):
            if (xs == ys) {
                // mem(head(ys), ys) is true.
            } else {
                // is_suffix_of(xs, ys0) holds.
                is_suffix_of_head_mem(xs, ys0); // Apply induction.
                // mem(head(xs), ys0) holds, so mem(head(xs), ys) holds.
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
    //@ open map(map, entries);
    if (map == 0) {
        //@ assert entries == nil;
        //@ close map(0, nil);
        return false;
    } else {
        //@ list<void *> map_keys = map(fst, entries);
        //@ assert map_keys == cons(?key_h, _);
        //@ is_suffix_of_head_mem(map_keys, keys);
        
        bool eq = equalsFunc(map->key, key);
        
        //@ assert eq == contains(eqKeys, key_h);
        
        if (eq) {
            //@ close map(map, entries);
            return true;
        } else {
            //@ list<void *> map_keys_tail = map(fst, tail(entries));
            //@ suffix_of_tail(map_keys_tail, key_h, keys);
            bool rec_result = map_contains_key(map->next, key, equalsFunc);
            //@ close map(map, entries);
            //@ assert rec_result == exists(map_keys_tail, (contains)(eqKeys));
            return rec_result;
        }
    }
}