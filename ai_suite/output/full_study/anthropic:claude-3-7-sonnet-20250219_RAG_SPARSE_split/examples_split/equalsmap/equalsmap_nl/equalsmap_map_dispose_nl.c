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
// Define a predicate for a linked list of map nodes
predicate map_nodes(struct node *map; int count) =
    map == 0 ?
        count == 0
    :
        map->next |-> ?next &*& 
        map->key |-> ?key &*& 
        map->value |-> ?value &*& 
        malloc_block_node(map) &*& 
        map_nodes(next, count - 1) &*&
        count > 0;
@*/

/**
 * Description:
 * The `map_dispose` function frees of all nodes in the map.
 *
 * @param map The head node of the map to be disposed of
 * 
 * This function makes sure that all nodes in the map are freed.
 */
void map_dispose(struct node *map)
//@ requires map_nodes(map, ?count);
//@ ensures true;
{
    //@ open map_nodes(map, count);
    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
    //@ else { assert count == 0; }
}