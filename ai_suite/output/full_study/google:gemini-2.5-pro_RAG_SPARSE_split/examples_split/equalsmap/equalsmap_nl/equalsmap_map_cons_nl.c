#include "stdlib.hh"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};

/*@
predicate map(struct node *head; list<pair<void *, void *> > kvs) =
    head == 0 ?
        kvs == nil
    :
        head->next |-> ?next &*&
        head->key |-> ?key &*&
        head->value |-> ?value &*&
        malloc_block_node(head) &*&
        map(next, ?tail_kvs) &*&
        kvs == cons(pair(key, value), tail_kvs);
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
struct node *map_cons(void *key, void *value, struct node *tail)
    //@ requires map(tail, ?tail_kvs);
    //@ ensures map(result, cons(pair(key, value), tail_kvs));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    //@ close map(n, cons(pair(key, value), tail_kvs));
    return n;
}