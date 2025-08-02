#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};

/*@
// Define a predicate for a map node
predicate node(struct node *n; void *k, void *v, struct node *next) =
    n != 0 &*&
    n->key |-> k &*&
    n->value |-> v &*&
    n->next |-> next &*&
    malloc_block_node(n);

// Define a predicate for a map (linked list of nodes)
predicate map(struct node *map; list<pair<void*, void*> > entries) =
    map == 0 ?
        entries == nil
    :
        node(map, ?k, ?v, ?next) &*&
        map(next, ?tail) &*&
        entries == cons(pair(k, v), tail);

// Define a predicate for a foo struct
predicate foo(struct foo *f; int value) =
    f != 0 &*&
    f->value |-> value &*&
    malloc_block_foo(f);
@*/

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
//@ requires map(tail, ?entries);
//@ ensures map(result, cons(pair(key, value), entries));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n, key, value, tail);
    //@ close map(n, cons(pair(key, value), entries));
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
//@ requires map(map, ?entries);
//@ ensures true;
{
    //@ open map(map, entries);
    if (map != 0) {
        //@ open node(map, _, _, _);
        map_dispose(map->next);
        free(map);
    }
}


/**
 * Description:
 * The `equalsFuncType` function checks if the two given keys equal.
 * 
 * It can have different implementations.
 */
typedef bool equalsFuncType(void *key, void *key0);
//@ requires true;
//@ ensures true;


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
//@ requires map(map, ?entries) &*& is_equalsFuncType(equalsFunc) == true;
//@ ensures map(map, entries) &*& result == exists(pair<void*, void*> p; mem(p, entries) && equalsFunc(p.fst, key));
{
    //@ open map(map, entries);
    if (map == 0)
        return false;
    else {
        //@ open node(map, ?k, ?v, ?next);
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            //@ close node(map, k, v, next);
            //@ close map(map, entries);
            return true;
        } else {
            bool result = map_contains_key(map->next, key, equalsFunc);
            //@ close node(map, k, v, next);
            //@ close map(map, entries);
            return result;
        }
    }
}



/**
 * Description:
 * The `foo_equals` function compares two foo structures for equality based on their `value` members.
 *
 * @param f1 Pointer to the first foo structure.
 * @param f2 Pointer to the second foo structure.
 * @return True if the `value` members of the two foo structures are equal, otherwise false.
 */
bool foo_equals(struct foo *f1, struct foo *f2)
//@ requires foo(f1, ?v1) &*& foo(f2, ?v2);
//@ ensures foo(f1, v1) &*& foo(f2, v2) &*& result == (v1 == v2);
{
    //@ open foo(f1, v1);
    //@ open foo(f2, v2);
    bool result = f1->value == f2->value;
    //@ close foo(f1, v1);
    //@ close foo(f2, v2);
    return result;
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


// TODO: make this function pass the verification
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
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);
 
    /*@
    // Define a wrapper function for foo_equals that matches the equalsFuncType signature
    predicate_family_instance equalsFuncType_pre(foo_equals)() = true;
    predicate_family_instance equalsFuncType_post(foo_equals)(bool result) = true;
    
    lemma void foo_equals_is_equalsFuncType()
      requires is_foo_equals(foo_equals) == true;
      ensures is_equalsFuncType(foo_equals) == true;
    {
      produce_function_pointer_chunk foo_equals() : equalsFuncType {
        call();
      }
    }
    @*/
    
    //@ foo_equals_is_equalsFuncType();
    bool c = map_contains_key(map, fooX, foo_equals);
    //@ assert c == true;
    assert(c);
   
    c = map_contains_key(map, fooY, foo_equals);
    //@ assert c == false;
    assert(!c);

    //@ open foo(foo1, _);
    //@ open foo(foo2, _);
    //@ open foo(foo3, _);
    //@ open foo(fooX, _);
    //@ open foo(fooY, _);
    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}