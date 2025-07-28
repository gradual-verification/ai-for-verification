#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};


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


