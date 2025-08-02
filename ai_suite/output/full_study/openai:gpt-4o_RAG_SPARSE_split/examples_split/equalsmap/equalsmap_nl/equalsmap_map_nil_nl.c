#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};

//@ predicate map_nil(struct node *n) = n == 0;

// TODO: make this function pass the verification
/**
 * Description:
 * The `map_nil` function returns a null pointer.
 *
 * It makes sure that the return value is a null pointer (representing an empty map).
 */
//@ requires true;
//@ ensures map_nil(result);
struct node *map_nil()
{
    return 0;
}