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
@*/

struct foo {
    int value;
};

/*@

predicate foo(pair<struct foo *, int> fv;) =
    switch (fv) {
        case pair(f, v): return f->value |-> v &*& malloc_block_foo(f);
    };

fixpoint int assoc<a, b>(list<pair<a, b> > xys, a x) {
    switch (xys) {
        case nil: return default_value;
        case cons(xy, xys0): return fst(xy) == x ? snd(xy) : assoc(xys0, x);
    }
}

// --- New contracts for the equality function and map_contains_key ---

predicate_family key_equals_pre(void* func)(void* key, void* data);
predicate_family key_equals_post(void* func)(void* key, void* data, bool result);
fixpoint bool key_equals_spec(void* func, void* key, void* data);

typedef bool equalsFuncType(void* key, void* data);
    //@ requires key_equals_pre(this)(key, data);
    //@ ensures key_equals_post(this)(key, data, result) &*& result == key_equals_spec(this, key, data);

lemma void key_equals_post_spec(void* func, void* key, void* data, bool result);
    requires key_equals_post(func)(key, data, result);
    ensures key_equals_post(func)(key, data, result) &*& result == key_equals_spec(func, key, data);

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
    //@ close map(result, cons(pair(key, value), tailEntries));
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

/*@
lemma void foreach_remove_lemma<t>(list<t> xs, predicate(t) p, t x)
    requires [?f]foreach(xs, p) &*& mem(x, xs) == true;
    ensures [f]foreach(remove(x, xs), p) &*& [f]p(x);
{
    open [f]foreach(xs, p);
    switch(xs) {
        case nil:
        case cons(h, t):
            if (h == x) {
            } else {
                foreach_remove_lemma(t, p, x);
                close [f]foreach(remove(x, xs), p);
            }
    }
}

lemma void foreach_unremove_lemma<t>(list<t> xs, predicate(t) p, t x)
    requires [?f]foreach(remove(x, xs), p) &*& [f]p(x) &*& mem(x, xs) == true;
    ensures [f]foreach(xs, p);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            if (h == x) {
                close [f]foreach(xs, p);
            } else {
                open [f]foreach(remove(x, xs), p);
                foreach_unremove_lemma(t, p, x);
                close [f]foreach(xs, p);
            }
    }
}
@*/

bool map_contains_key(struct node *map, void *data, equalsFuncType *equalsFunc)
    //@ requires map(map, ?entries) &*& is_equalsFuncType(equalsFunc) == true &*& foreach(map(fst, entries), (k) => key_equals_pre(equalsFunc)(k, data));
    //@ ensures map(map, entries) &*& foreach(map(fst, entries), (k) => key_equals_post(equalsFunc)(k, data, _)) &*& result == exists(map(fst, entries), (k) => key_equals_spec(equalsFunc, k, data));
{
    //@ open foreach(map(fst, entries), (k) => key_equals_pre(equalsFunc)(k, data));
    if (map == 0) {
        return false;
    } else {
        //@ open map(map, entries);
        bool eq = equalsFunc(map->key, data);
        //@ key_equals_post_spec(equalsFunc, map->key, data, eq);
        if (eq) {
            //@ close map(map, entries);
            //@ close foreach(map(fst, entries), (k) => key_equals_post(equalsFunc)(k, data, _));
            return true;
        } else {
            bool res = map_contains_key(map->next, data, equalsFunc);
            //@ close map(map, entries);
            //@ close foreach(map(fst, entries), (k) => key_equals_post(equalsFunc)(k, data, _));
            return res;
        }
    }
}

/*@
predicate_family_instance key_equals_pre(foo_equals)(void* key, void* data) =
    [1/2]foreach(?fvs, foo) &*& mem(key, map(fst, fvs)) == true &*& mem(data, map(fst, fvs)) == true;

predicate_family_instance key_equals_post(foo_equals)(void* key, void* data, bool result) =
    [1/2]foreach(?fvs, foo) &*& mem(key, map(fst, fvs)) == true &*& mem(data, map(fst, fvs)) == true;

fixpoint bool key_equals_spec(foo_equals, void* key, void* data) {
    return assoc(ghost_list_state, key) == assoc(ghost_list_state, data);
}

lemma void foo_equals_post_spec(void* key, void* data, bool result)
    requires key_equals_post(foo_equals)(key, data, result);
    ensures key_equals_post(foo_equals)(key, data, result) &*& result == key_equals_spec(foo_equals, key, data);
{
    open key_equals_post(foo_equals)(key, data, result);
    assert [1/2]foreach(?fvs, foo);
    if (key == data) {
        assert assoc(fvs, key) == assoc(fvs, data);
    } else {
        foreach_remove_lemma(fvs, foo, pair(key, assoc(fvs, key)));
        open foo(pair(key, assoc(fvs, key)));
        list<pair<void*, int> > fvs_without_key = remove(pair(key, assoc(fvs, key)), fvs);
        foreach_remove_lemma(fvs_without_key, foo, pair(data, assoc(fvs, data)));
        open foo(pair(data, assoc(fvs, data)));
        
        assert ((struct foo*)key)->value |-> assoc(fvs, key);
        assert ((struct foo*)data)->value |-> assoc(fvs, data);
        
        close foo(pair(data, assoc(fvs, data)));
        foreach_unremove_lemma(fvs_without_key, foo, pair(data, assoc(fvs, data)));
        close foo(pair(key, assoc(fvs, key)));
        foreach_unremove_lemma(fvs, foo, pair(key, assoc(fvs, key)));
    }
    close key_equals_post(foo_equals)(key, data, result);
}

@*/

bool foo_equals(void *f1, void *f2) //@ : equalsFuncType
    //@ requires key_equals_pre(foo_equals)(f1, f2);
    //@ ensures key_equals_post(foo_equals)(f1, f2, result) &*& result == key_equals_spec(foo_equals, f1, f2);
{
    //@ open key_equals_pre(foo_equals)(f1, f2);
    //@ assert [1/2]foreach(?fvs, foo);
    //@ ghost_list_state = fvs;
    //@ foo_equals_post_spec(f1, f2, ((struct foo*)f1)->value == ((struct foo*)f2)->value);
    //@ close key_equals_post(foo_equals)(f1, f2, ((struct foo*)f1)->value == ((struct foo*)f2)->value);
    return ((struct foo*)f1)->value == ((struct foo*)f2)->value;
}


struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures foo(pair(result, value));
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    //@ close foo(pair(result, value));
    return foo;
}


// TODO: make this function pass the verification
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
    
    //@ list<pair<void*, int> > fvs = cons(pair(foo1, 100), cons(pair(foo2, 200), cons(pair(foo3, 300), cons(pair(fooX, 200), cons(pair(fooY, 400), nil)))));
    //@ close foreach(fvs, foo);
    
    //@ assert map(map, ?entries);
    //@ list<void*> map_keys = map(fst, entries);
    
    /*@
    predicate P(void* k) = key_equals_pre(foo_equals)(k, fooX);
    
    lemma void create_pre()
        requires [1/2]foreach(fvs, foo) &*& mem(?k, map_keys) == true;
        ensures P(k);
    {
        open [1/2]foreach(fvs, foo);
        assert mem(k, map(fst, fvs)) == true;
        assert mem(fooX, map(fst, fvs)) == true;
        close key_equals_pre(foo_equals)(k, fooX);
        close P(k);
    }
    
    produce_lemma_function_pointer_chunk(create_pre) : foreach_pred_arg_type<void*>(P)() {
        open P(?k);
        call();
    }
    
    close foreach_stub(P, map_keys);
    @*/
    
    //@ ghost_list_state = fvs;
    bool c = map_contains_key(map, fooX, foo_equals);
    assert(c);
    
    /*@
    predicate Q(void* k) = key_equals_pre(foo_equals)(k, fooY);
    
    lemma void create_pre_2()
        requires [1/2]foreach(fvs, foo) &*& mem(?k, map_keys) == true;
        ensures Q(k);
    {
        open [1/2]foreach(fvs, foo);
        assert mem(k, map(fst, fvs)) == true;
        assert mem(fooY, map(fst, fvs)) == true;
        close key_equals_pre(foo_equals)(k, fooY);
        close Q(k);
    }
    
    produce_lemma_function_pointer_chunk(create_pre_2) : foreach_pred_arg_type<void*>(Q)() {
        open Q(?k);
        call();
    }
    
    close foreach_stub(Q, map_keys);
    @*/
    
    //@ ghost_list_state = fvs;
    c = map_contains_key(map, fooY, foo_equals);
    assert(!c);
    
    //@ open foreach(fvs, foo);
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