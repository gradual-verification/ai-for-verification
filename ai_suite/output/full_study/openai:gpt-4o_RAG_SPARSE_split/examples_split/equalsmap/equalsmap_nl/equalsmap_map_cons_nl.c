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
predicate nodes(struct node *n, list<pair<void *, void *> > kvs) =
    n == 0 ?
        kvs == nil
    :
        n->key |-> ?key &*& n->value |-> ?value &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?kvs0) &*& kvs == cons(pair(key, value), kvs0);
@*/

// TODO: make this function pass the verification
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
requires true;
ensures nodes(result, cons(pair(key, value), ?kvs)) &*& result != 0;
@*/
struct node *map_cons(void *key, void *value, struct node *tail)
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close nodes(n, cons(pair(key, value), ?kvs));
    return n;
}