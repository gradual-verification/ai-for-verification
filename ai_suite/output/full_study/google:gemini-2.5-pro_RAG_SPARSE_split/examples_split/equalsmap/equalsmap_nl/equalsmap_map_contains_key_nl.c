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

// Predicate for a map node list
predicate map(struct node *n, list<pair<void *, void *> > entries) =
    n == 0 ?
        entries == nil
    :
        n->next |-> ?next &*&
        n->key |-> ?key &*&
        n->value |-> ?value &*&
        malloc_block_node(n) &*&
        map(next, ?tail_entries) &*&
        entries == cons(pair(key, value), tail_entries);

// Helper fixpoint to get a list of keys from a list of entries
fixpoint list<void *> map_keys(list<pair<void *, void *> > entries) {
    return map(fst, entries);
}

// Abstract fixpoint to model the behavior of the equality function
fixpoint bool key_eq(void *f, void *k1, void *k2);

// Predicate family to hold the data associated with a key, indexed by the equality function
predicate_family key_data(void *p)(void *key);

// Fixpoint to model the behavior of map_contains_key
fixpoint bool list_contains(list<void *> ks, void *k, void *f) {
    switch (ks) {
        case nil: return false;
        case cons(h, t): return key_eq(f, h, k) || list_contains(t, k, f);
    }
}

@*/


/**
 * Description:
 * The `equalsFuncType` function checks if the two given keys equal.
 * 
 * It can have different implementations.
 */
typedef bool equalsFuncType(void *key, void *key0);
    //@ requires key_data(this)(key) &*& key_data(this)(key0);
    //@ ensures key_data(this)(key) &*& key_data(this)(key0) &*& result == key_eq(this, key, key0);


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
bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
    //@ requires map(map, ?entries) &*& is_equalsFuncType(equalsFunc) == true &*& key_data(equalsFunc)(key) &*& foreach(map_keys(entries), key_data(equalsFunc));
    //@ ensures map(map, entries) &*& key_data(equalsFunc)(key) &*& foreach(map_keys(entries), key_data(equalsFunc)) &*& result == list_contains(map_keys(entries), key, equalsFunc);
{
   
    //@ open map(map, entries);
    if (map == 0) {
        //@ close map(0, nil);
        return false;
    } else {
        //@ open foreach(map_keys(entries), key_data(equalsFunc));
        //@ assert map->key |-> ?map_key;
        
        bool eq = equalsFunc(map->key, key);
        
        if (eq) {
            //@ close foreach(map_keys(entries), key_data(equalsFunc));
            //@ close map(map, entries);
            return true;
        } else {
            //@ assert map->next |-> ?next;
            bool rec_result = map_contains_key(map->next, key, equalsFunc);
            //@ close foreach(map_keys(entries), key_data(equalsFunc));
            //@ close map(map, entries);
            return rec_result;
        }
    }
}