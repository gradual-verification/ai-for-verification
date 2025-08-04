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
        malloc_block_node(n) &*&
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
        case pair(f, v): return f->value |-> v &*& malloc_block_foo(f);
    };

fixpoint b assoc<a, b>(list<pair<a, b> > xys, a x) {
    switch (xys) {
        case nil: return default_value;
        case cons(xy, xys0): return fst(xy) == x ? snd(xy) : assoc(xys0, x);
    }
}

lemma void mem_map_fst_mem_assoc<a, b>(list<pair<a, b>> xys, a x)
    requires distinct(map(fst, xys)) == true &*& mem(x, map(fst, xys)) == true;
    ensures mem(pair(x, assoc(xys, x)), xys) == true;
{
    switch (xys) {
        case nil:
        case cons(h, t):
            if (fst(h) == x) {
            } else {
                mem_map_fst_mem_assoc(t, x);
            }
    }
}

lemma void assoc_eq_v_iff_mem_eqKeys<a, b>(list<pair<a, b>> fvs, a f1, b v)
    requires distinct(map(fst, fvs)) == true &*& mem(f1, map(fst, fvs)) == true;
    ensures (assoc(fvs, f1) == v) == mem(f1, map(fst, filter((p) => snd(p) == v, fvs)));
{
    switch (fvs) {
        case nil:
        case cons(h, t):
            if (fst(h) == f1) {
            } else {
                assoc_eq_v_iff_mem_eqKeys(t, f1, v);
            }
    }
}

lemma void is_suffix_of_map_append<a, b, c>(fixpoint(a, b) f, list<a> xs, list<a> ys)
    requires true;
    ensures is_suffix_of(map(f, ys), map(f, append(xs, ys))) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            is_suffix_of_map_append(f, t, ys);
    }
}

@*/


struct node *map_nil()
    //@ requires true;
    //@ ensures map(result, nil);
{
    return 0;
}


struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires map(tail, ?tailEntries);
    //@ ensures map(result, cons(pair(key, value), tailEntries));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close map(n, cons(pair(key, value), tailEntries));
    return n;
}


void map_dispose(struct node *map)
    //@ requires map(map, _);
    //@ ensures true;
{
    //@ open map(map, _);
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}


typedef bool equalsFuncType/*@ (list<void *> keys, void *key00, list<void *> eqKeys, predicate() p) @*/(void *key, void *key0);
    //@ requires p() &*& mem(key, keys) == true &*& key0 == key00;
    //@ ensures p() &*& result == contains(eqKeys, key);



bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires [_]is_equalsFuncType(equalsFunc, ?keys, key, ?eqKeys, ?p) &*& p() &*& map(map, ?entries) &*& is_suffix_of(map((fst), entries), keys) == true;
    //@ ensures p() &*& map(map, entries) &*& result == exists(map((fst), entries), (contains)(eqKeys));
{
    //@ open map(map, entries);
    if (map == 0)
        return false;
    else {
        //@ is_suffix_of_cons(map((fst), tail(entries)), keys);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close map(map, entries);
            return true;
        } else {
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ close map(map, entries);
            return res;
        }
    }
}


bool foo_equals(void *f1_void, void *f2_void) //@ : equalsFuncType
    /*@ requires
        exists<list<pair<void *, int> > >(?fvs) &*&
        exists<int>(?v) &*&
        distinct(map(fst, fvs)) == true &*&
        let keys = map(fst, fvs) in
        let p = (foreach(fvs, foo) &*& ((struct foo *)f2_void)->value |-> v) in
        let eqKeys = map(fst, filter((p_fv) => snd(p_fv) == v, fvs)) in
        is_equalsFuncType(this, keys, f2_void, eqKeys, p) &*&
        p() &*& mem(f1_void, keys) == true;
    @*/
    /*@ ensures
        exists<list<pair<void *, int> > >(?fvs) &*&
        exists<int>(?v) &*&
        distinct(map(fst, fvs)) == true &*&
        let keys = map(fst, fvs) in
        let p = (foreach(fvs, foo) &*& ((struct foo *)f2_void)->value |-> v) in
        let eqKeys = map(fst, filter((p_fv) => snd(p_fv) == v, fvs)) in
        is_equalsFuncType(this, keys, f2_void, eqKeys, p) &*&
        p() &*& result == (assoc(fvs, f1_void) == v);
    @*/
{
    //@ open p();
    //@ assert foreach(fvs, foo) &*& ((struct foo *)f2_void)->value |-> v;
    //@ mem_map_fst_mem_assoc(fvs, f1_void);
    //@ foreach_remove(pair(f1_void, assoc(fvs, f1_void)), fvs);
    //@ open foo(pair(f1_void, assoc(fvs, f1_void)));
    struct foo *f1 = f1_void;
    struct foo *f2 = f2_void;
    bool res = f1->value == f2->value;
    //@ close foo(pair(f1_void, assoc(fvs, f1_void)));
    //@ foreach_unremove(pair(f1_void, assoc(fvs, f1_void)), fvs);
    //@ close p();
    //@ assoc_eq_v_iff_mem_eqKeys(fvs, f1_void, v);
    return res;
}


struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures foo(pair(result, value));
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    //@ close foo(pair(foo, value));
    return foo;
}


int main()
    //@ requires true;
    //@ ensures true;
{
    struct foo *foo1 = create_foo(100);
    struct foo *foo2 = create_foo(200);
    struct foo *foo3 = create_foo(300);
    struct node *map = map_nil();
    map = map_cons(foo3, 0, map);
    map = map_cons(foo2, 0, map);
    map = map_cons(foo1, 0, map);
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);
  
    //@ list<pair<void *, int> > fvs_map = cons(pair(foo1, 100), cons(pair(foo2, 200), cons(pair(foo3, 300), nil)));
    //@ list<pair<void *, int> > fvs_extra = cons(pair(fooX, 200), cons(pair(fooY, 400), nil));
    //@ list<pair<void *, int> > all_fvs = append(fvs_extra, fvs_map);
    //@ close foreach(fvs_map, foo);
    //@ close foreach(fvs_extra, foo);
    //@ foreach_append(fvs_extra, fvs_map);
    
    //@ list<void *> all_keys = map(fst, all_fvs);
    //@ list<void *> map_keys = map((fst), map((fst), entries));
    //@ list<pair<void *, void *> > entries = cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil)));
    //@ is_suffix_of_map_append(fst, fvs_extra, fvs_map);

    //@ list<void *> eq_keys_X = cons(foo2, cons(fooX, nil));
    //@ predicate() p_X = foreach(all_fvs, foo) &*& fooX->value |-> 200;
    //@ close p_X();
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ open p_X();
    //@ assert exists(map_keys, (contains)(eq_keys_X)) == (contains(eq_keys_X, foo1) || contains(eq_keys_X, foo2) || contains(eq_keys_X, foo3));
    assert(c);

    //@ list<void *> eq_keys_Y = cons(fooY, nil);
    //@ predicate() p_Y = foreach(all_fvs, foo) &*& fooY->value |-> 400;
    //@ close p_Y();
    c = map_contains_key(map, fooY, foo_equals);
    //@ open p_Y();
    //@ assert exists(map_keys, (contains)(eq_keys_Y)) == (contains(eq_keys_Y, foo1) || contains(eq_keys_Y, foo2) || contains(eq_keys_Y, foo3));
    assert(!c);
    
    //@ open foreach(all_fvs, foo);
    //@ open foreach(fvs_extra, foo);
    //@ open foreach(fvs_map, foo);
    
    //@ open foo(pair(foo1, 100));
    free(foo1);
    //@ open foo(pair(foo2, 200));
    free(foo2);
    //@ open foo(pair(foo3, 300));
    free(foo3);
    //@ open foo(pair(fooX, 200));
    free(fooX);
    //@ open foo(pair(fooY, 400));
    free(fooY);
    
    map_dispose(map);
    return 0;
}