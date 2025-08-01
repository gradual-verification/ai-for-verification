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
 * The `map_nil` function returns a null pointer.
 *
 * It makes sure that the return value is a null pointer (representing an empty map).
 */
struct node *map_nil()
{
    return 0;
}

