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
 * The `create_foo` function dynamically allocates memory for a foo structure
 * and initializes its `value` member with the provided value.
 *
 * @param value The value to be assigned to the `value` member of the created foo structure.
 * @return Pointer to the newly created foo structure.
 * 
 * It makes sure that the return value is a foo structure with the given value.
 */
struct foo *create_foo(int value);
{
    struct foo *foo = malloc(sizeof(struct foo));
