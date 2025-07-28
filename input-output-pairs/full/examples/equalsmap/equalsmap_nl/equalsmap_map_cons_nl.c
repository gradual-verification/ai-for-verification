#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};


    if (foo == 0) abort();
    foo->value = value;
    return foo;
}


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
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}

