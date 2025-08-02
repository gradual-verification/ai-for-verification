#include "stdlib.h"
#include "stdbool.h"

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
 * The `equalsFuncType` function checks if the two given keys equal.
 * 
 * It can have different implementations.
 */
typedef bool equalsFuncType(void *key, void *key0);

//@ predicate nodes(struct node *n, list<void *> keys) = n == 0 ? keys == nil : n->key |-> ?k &*& n->value |-> _ &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?nextKeys) &*& keys == cons(k, nextKeys);

//@ predicate map(struct node *n, list<void *> keys) = nodes(n, keys);

/*@

predicate_family_instance equalsFuncType_spec(equalsFuncType *f)(void *key1, void *key2) =
    requires true;
    ensures result == (key1 == key2);

@*/

// TODO: make this function pass the verification
/**
 * Description:
 * The `map_contains_key` function checks if the given key exists in the map by recursively traversing through the map nodes.
 *
 * @param map        The head node of the map to search.
 * @param key        The key to search for.
 * @param equalsFunc A function pointer used to compare keys for equality.
 * @return           True if the key exists in the map, otherwise false.
 */
//@ requires map(map, ?keys) &*& is_equalsFuncType_spec(equalsFunc, equalsFuncType_spec);
//@ ensures map(map, keys) &*& result == mem(key, keys);
bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
{
    //@ open map(map, keys);
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
    //@ close map(map, keys);
}