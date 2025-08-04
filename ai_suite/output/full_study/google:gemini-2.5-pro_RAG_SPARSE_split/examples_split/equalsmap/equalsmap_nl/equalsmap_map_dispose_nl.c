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
// A predicate to represent a singly-linked list of map nodes.
// 'n' is the pointer to the head of the list.
// 'kvs' is a ghost list of key-value pairs, representing the abstract state.
predicate map_nodes(struct node *n; list<pair<void*, void*> > kvs) =
    n == 0 ?
        // Base case: A null pointer represents an empty list.
        kvs == nil
    :
        // Recursive step: A non-null pointer points to a valid node.
        // We must own the memory for the node's fields...
        n->next |-> ?next &*&
        n->key |-> ?key &*&
        n->value |-> ?value &*&
        // ...and the memory block for the struct itself.
        malloc_block_node(n) &*&
        // The rest of the list is described by a recursive call on the 'next' pointer.
        map_nodes(next, ?tail_kvs) &*&
        // The abstract list of key-value pairs is built by prepending the current pair.
        kvs == cons(pair(key, value), tail_kvs);
@*/


// TODO: make this function pass the verification
/**
 * Description:
 * The `map_dispose` function frees of all nodes in the map.
 *
 * @param map The head node of the map to be disposed of
 * 
 * This function makes sure that all nodes in the map are freed.
 */
void map_dispose(struct node *map)
    //@ requires map_nodes(map, _);
    //@ ensures true;
{
    //@ open map_nodes(map, _);
    if (map != 0) {
        // The recursive call consumes the predicate for the rest of the list.
        map_dispose(map->next);
        // After the rest of the list is freed, free the current node.
        free(map);
    }
}