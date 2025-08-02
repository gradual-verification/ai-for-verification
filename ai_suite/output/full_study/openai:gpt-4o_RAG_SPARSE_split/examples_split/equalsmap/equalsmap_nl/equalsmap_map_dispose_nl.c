#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

//@ predicate nodes(struct node *n;) = n == 0 ? true : n->next |-> ?next &*& n->key |-> ?key &*& n->value |-> ?value &*& malloc_block(n, sizeof(struct node)) &*& nodes(next);

// TODO: make this function pass the verification
/**
 * Description:
 * The `map_dispose` function frees all nodes in the map.
 *
 * @param map The head node of the map to be disposed of
 * 
 * This function makes sure that all nodes in the map are freed.
 */
void map_dispose(struct node *map)
    //@ requires nodes(map);
    //@ ensures true;
{
    //@ open nodes(map);
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}