#include "stdlib.h"

/*@
// Define a predicate for a node in the map
predicate node(struct node *n; void *key, void *value, struct node *next) =
    n->next |-> next &*&
    n->key |-> key &*&
    n->value |-> value &*&
    malloc_block_node(n);

// Define a predicate for a map (linked list of key-value pairs)
predicate map(struct node *head) =
    head == 0 ? emp : 
    node(head, ?k, ?v, ?next) &*& map(next);
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
 * The `map_cons` function creates a new node with the given key and value, and attaches it to the provided tail node.
 *
 * @param key The key to be stored in the new node.
 * @param value The value to be stored in the new node.
 * @param tail The tail node to which the new node will be attached.
 * 
 * It makes sure that the return value is a pointer to the newly created node, 
 * which contains the key and value and is the head of the map.
 */
/*@
// Function contract
requires map(tail) &*& pointer_within_limits(key) == true &*& pointer_within_limits(value) == true;
ensures map(result) &*& node(result, key, value, tail);
@*/
struct node *map_cons(void *key, void *value, struct node *tail)
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close node(n, key, value, tail);
    return n;
}