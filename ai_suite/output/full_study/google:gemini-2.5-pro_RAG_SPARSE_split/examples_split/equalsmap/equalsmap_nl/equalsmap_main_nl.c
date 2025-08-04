#include "stdlib.h"
#include "stdbool.h"
#include "assert.h"

/*@
// Predicate for a foo struct, holding its value.
predicate foo(struct foo *f; int value) =
    f->value |-> value &*& malloc_block_foo(f);

// Predicate for a map node, forming a linked list of key-value pairs.
// The map is represented by a ghost list of pairs.
predicate map(struct node *n, list<pair<void *, void *> > kvs) =
    n == 0 ?
        kvs == nil
    :
        n->key |-> ?key &*&
        n->value |-> ?value &*&
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        map(next, ?tail_kvs) &*&
        kvs == cons(pair(key, value), tail_kvs);

// Ghost function to extract keys from a list of key-value pairs.
fixpoint list<void *> map_keys(list<pair<void *, void *> > kvs) {
    return map(fst, kvs);
}

// Predicate for a list of foo structs.
// It holds the foo predicate for each element in the list of pointers.
predicate foos(list<void*> ps, list<int> vs) =
    switch (ps) {
        case nil: return vs == nil;
        case cons(h, t):
            return foo((struct foo*)h, ?v) &*& foos(t, ?t_vs) &*& vs == cons(v, t_vs);
    };

// Predicate family for the data required by the equals function.
// The function pointer itself is the family index.
predicate_family equals_pred(void *func)(void *key1, void *key2);
@*/

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};


/**
 * Description:
 * The `map_nil` function returns a null pointer.
 *
 * It makes sure that the return value is a null pointer (representing an empty map).
 */
struct node *map_nil()
    //@ requires true;
    //@ ensures map(result, nil);
{
    //@ close map(0, nil);
    return 0;
}


/**
 * Description:
 * The `map_cons` function creates a new node with the given key and value, and attaches it to the provided tail node.
 *
 * @param key The key to be stored in the new node.
 * @param value The value to be stored in the new node.
 * @param tail The tail node to which the new node will be attached.
 * 
 * It makes sure that the return value is a pointer to the newly created node, 
 * which contains the key and value and is the head of the map.
 */
struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires map(tail, ?kvs_tail);
    //@ ensures map(result, cons(pair(key, value), kvs_tail));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close map(n, cons(pair(key, value), kvs_tail));
    return n;
}


/**
 * Description:
 * The `map_dispose` function frees of all nodes in the map.
 *
 * @param map The head node of the map to be disposed of
 * 
 * This function makes sure that all nodes in the map are freed.
 */
void map_dispose(struct node *map)
    //@ requires map(map, ?kvs);
    //@ ensures true;
{
    if (map != 0) {
        //@ open map(map, kvs);
        map_dispose(map->next);
        free(map);
    } else {
        //@ open map(map, kvs);
    }
}


/**
 * Description:
 * The `equalsFuncType` function checks if the two given keys equal.
 * 
 * It can have different implementations.
 */
typedef bool equalsFuncType(void *key, void *key0);
    //@ requires equals_pred(this)(key, key0);
    //@ ensures equals_pred(this)(key, key0);


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
    //@ requires map(map, ?kvs) &*& foos(map_keys(kvs), ?key_values) &*& foo(key, ?search_value) &*& is_equalsFuncType(equalsFunc) == true &*& equalsFunc == foo_equals;
    //@ ensures map(map, kvs) &*& foos(map_keys(kvs), key_values) &*& foo(key, search_value) &*& result == mem(search_value, key_values);
{
    //@ open map(map, kvs);
    //@ open foos(map_keys(kvs), key_values);
    if (map == 0) {
        return false;
    } else {
        //@ void *map_key = map->key;
        
        //@ close equals_pred(foo_equals)(map_key, key);
        bool eq = equalsFunc(map_key, key);
        //@ open equals_pred(foo_equals)(map_key, key);
        
        //@ assert eq == (head(key_values) == search_value);
        
        if (eq) {
            //@ mem_head(search_value, key_values);
            //@ close foos(map_keys(kvs), key_values);
            //@ close map(map, kvs);
            return true;
        } else {
            //@ assert head(key_values) != search_value;
            bool res = map_contains_key(map->next, key, equalsFunc);
            //@ assert res == mem(search_value, tail(key_values));
            //@ mem_non_head(search_value, key_values);
            //@ close foo((struct foo*)map_key, head(key_values));
            //@ close foos(map_keys(kvs), key_values);
            //@ close map(map, kvs);
            return res;
        }
    }
}


/*@
// Predicate family instance for foo_equals.
// It requires that both keys are valid foo pointers.
predicate_family_instance equals_pred(foo_equals)(void *key1, void *key2) =
    foo((struct foo *)key1, ?v1) &*& foo((struct foo *)key2, ?v2);
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
    //@ : equalsFuncType
    //@ requires equals_pred(foo_equals)(f1, f2);
    //@ ensures equals_pred(foo_equals)(f1, f2) &*& result == (((struct foo *)f1)->value == ((struct foo *)f2)->value);
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
 * 
 * It makes sure that the return value is a foo structure with the given value.
 */
struct foo *create_foo(int value)
    //@ requires true;
    //@ ensures foo(result, value);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    //@ close foo(foo, value);
    return foo;
}


/**
 * Description:
 * The `main` function checks whether the created map has and doesn't an element 
 * whose value equal to the value of the created one.
 */
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
    //@ list<pair<void*, void*> > kvs = cons(pair(foo1, 0), cons(pair(foo2, 0), cons(pair(foo3, 0), nil)));
    //@ list<void*> keys = map_keys(kvs);
    //@ list<int> key_values = cons(100, cons(200, cons(300, nil)));
    
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);
 
    //@ close foos(keys, key_values);
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ assert c == mem(200, key_values);
    //@ mem_cons(200, cons(100, cons(200, cons(300, nil))));
    assert(c);
   
    c = map_contains_key(map, fooY, foo_equals);
    //@ assert c == mem(400, key_values);
    assert(!c);

    //@ open foos(keys, key_values);
    //@ open foos(tail(keys), tail(key_values));
    //@ open foos(tail(tail(keys)), tail(tail(key_values)));
    //@ open foos(nil, nil);
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}