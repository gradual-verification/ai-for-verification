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
/**
 * Description:
 * The `map_nil` function returns a null pointer, indicating the end of a mapped list.
 *
 * @returns A null pointer.
 */
struct node *map_nil()
//requires true;
//ensures true;
{
    return 0;
}
/**
 * Description:
 * The `map_cons` function creates a new node with the given key and value, and attaches it to the provided tail node.
 *
 * @param key The key to be stored in the new node.
 * @param value The value to be stored in the new node.
 * @param tail The tail node to which the new node will be attached.
 * @returns A pointer to the newly created node.
 */
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
/**
 * Description:
 * The `map_dispose` function recursively frees of all nodes in the map, starting from the given node.
 *
 * @param map The head node of the map to be disposed of.
 */
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

/*@

fixpoint bool eq<t>(unit u, t x, t y) {
    switch (u) {
        case unit: return x == y;
    }
}

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

lemma void is_suffix_of_mem<t>(list<t> xs, list<t> ys, t y)
    requires is_suffix_of(xs, ys) == true &*& mem(y, xs) == true;
    ensures mem(y, ys) == true;
{
    switch (ys) {
        case nil:
        case cons(y0, ys0):
            if (xs == ys) {
            } else {
                if (y0 == y) {
                } else {
                    is_suffix_of_mem(xs, ys0, y);
                }
            }
    }
}

lemma void is_suffix_of_trans<t>(list<t> xs, list<t> ys, list<t> zs)
    requires is_suffix_of(xs, ys) == true &*& is_suffix_of(ys, zs) == true;
    ensures is_suffix_of(xs, zs) == true;
{
    switch (zs) {
        case nil:
        case cons(z, zs0):
            if (zs == ys) {
            } else {
                is_suffix_of_trans(xs, ys, zs0);
            }
    }
}

lemma_auto void is_suffix_of_refl<t>(list<t> xs)
    requires true;
    ensures is_suffix_of(xs, xs) == true;
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
    }
}

@*/
/**
 * Description:
 * The `map_contains_key` function checks if the given key exists in the map by recursively traversing through the map nodes.
 *
 * @param map        The head node of the map to search.
 * @param key        The key to search for.
 * @param equalsFunc A function pointer used to compare keys for equality.
 * @return           True if the key exists in the map, otherwise false.
 */
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
/**
 * Description:
 * The `foo_equals` function compares two foo structures for equality based on their `value` members.
 *
 * @param f1 Pointer to the first foo structure.
 * @param f2 Pointer to the second foo structure.
 * @return True if the `value` members of the two foo structures are equal, otherwise false.
 */
bool foo_equals(struct foo *f1, struct foo *f2)
     //@ requires foreach(?fvs, foo) &*& f2->value |-> ?value ;
    //@ ensures foreach(fvs, foo) &*& f2->value |-> value &*& result == (assoc(fvs, f1) == value);
{
    
    return f1->value == f2->value;
   
}
/**
 * Description:
 * The `create_foo` function dynamically allocates memory for a foo structure
 * and initializes its `value` member with the provided value.
 *
 * @param value The value to be assigned to the `value` member of the created foo structure.
 * @return Pointer to the newly created foo structure.
 */
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
