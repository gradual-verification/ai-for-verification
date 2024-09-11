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

struct node *map_nil()
//requires true;
//ensures true;
{
    return 0;
}

struct node *map_cons(void *key, void *value, struct node *tail)
//requires key!=NULL&*& value!=NULL&*& tail!=NULL;
//ensures n!=NULL;
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}

void map_dispose(struct node *map)
//requires map!=NULL;
//ensures true;
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
 //@ requires p() &*& map(map, ?entries) &*& is_suffix_of(map((fst), entries), keys) == true;
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

struct foo {
    int value;
};

/*@

predicate foo(pair<struct foo *, int> fv;) =
    switch (fv) {
        case pair(f, v): return f->value |-> v;
    };

predicate_ctor foos_ctor(list<pair<struct foo *, int> > fvs, struct foo *f, int value)() =
    foreach(fvs, foo) &*& f->value |-> value;

fixpoint b assoc<a, b>(list<pair<a, b> > xys, a x) {
    switch (xys) {
        case nil: return default_value;
        case cons(xy, xys0): return fst(xy) == x ? snd(xy) : assoc(xys0, x);
    }
}

@*/

bool foo_equals(struct foo *f1, struct foo *f2)
     //@ requires foreach(?fvs, foo) &*& f2->value |-> ?value ;
    //@ ensures foreach(fvs, foo) &*& f2->value |-> value &*& result == (assoc(fvs, f1) == value);
{
    
    return f1->value == f2->value;
   
}

struct foo *create_foo(int value);
    //@ requires true;
    //@ ensures result->value |-> value;
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
    
    bool c = map_contains_key(map, fooX, foo_equals);
    assert(c);

    c = map_contains_key(map, fooY, foo_equals);
    assert(!c);

    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}
