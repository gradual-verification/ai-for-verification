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
    return n;
}


void map_dispose(struct node *map)
    //@ requires map(map, _);
    //@ ensures true;
{
   
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
    
    if (map == 0)
        return false;
    else {
        
        bool eq = equalsFunc(map->key, key);
        if (eq)
            return true;
        else {
         
            return map_contains_key(map->next, key, equalsFunc);
        }
    }
}



bool foo_equals(struct foo *f1, struct foo *f2)
    //@ requires foreach(?fvs, foo) &*& f2->value |-> ?value &*& mem(pair(f1, assoc(fvs, f1)), fvs) == true;
    //@ ensures foreach(fvs, foo) &*& f2->value |-> value &*& result == (assoc(fvs, f1) == value);
{

    return f1->value == f2->value;

}


struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures result->value |-> value &*& malloc_block_foo(result);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
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
    
    //@ close foo(pair(foo1, 100));
    //@ close foo(pair(foo2, 200));
    //@ close foo(pair(foo3, 300));
    //@ close foreach(cons(pair(foo1, 100), cons(pair(foo2, 200), cons(pair(foo3, 300), nil))), foo);
    
    //@ assert map(map, cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil))));
    //@ assert map((fst), cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil)))) == cons(foo1, cons(foo2, cons(foo3, nil)));
    
    //@ assert is_suffix_of(cons(foo1, cons(foo2, cons(foo3, nil))), cons(foo1, cons(foo2, cons(foo3, nil)))) == true;
    
    //@ predicate foo_equals_context() = foreach(cons(pair(foo1, 100), cons(pair(foo2, 200), cons(pair(foo3, 300), nil))), foo) &*& fooX->value |-> 200;
    //@ close foo_equals_context();
    
    //@ produce_lemma_function_pointer_chunk foo_equals: foo_equals(foo2, fooX) |-> ?result;
    //@ close is_equalsFuncType(foo_equals, cons(foo1, cons(foo2, cons(foo3, nil))), fooX, cons(foo2, nil), foo_equals_context);
    
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ open foo_equals_context();
    assert(c);

    //@ close foo_equals_context();
    //@ produce_lemma_function_pointer_chunk foo_equals: foo_equals(foo2, fooY) |-> ?result2;
    //@ close is_equalsFuncType(foo_equals, cons(foo1, cons(foo2, cons(foo3, nil))), fooY, cons(foo2, nil), foo_equals_context);
    
    c = map_contains_key(map, fooY, foo_equals);
    //@ open foo_equals_context();
    assert(!c);
    
    //@ open foreach(_, foo);
    //@ open foo(_);
    //@ open foreach(_, foo);
    //@ open foo(_);
    //@ open foreach(_, foo);
    //@ open foo(_);
    
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}