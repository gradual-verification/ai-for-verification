#include <stdlib.h>

struct node {
    struct node *next;
};

//@ predicate nodes(struct node *n; list<struct node *> nodes) = 
//@     n == 0 ? 
//@         nodes == nil 
//@     : 
//@         n->next |-> ?next &*& malloc_block(n, sizeof(struct node)) &*& nodes(next, ?nodes0) &*& nodes == cons(n, nodes0);

// TODO: make this function pass the verification
/***
 * Description:
 * The `create_list` function creates an empty list.
 *
 * It makes sure that the return value is the head of a list. 
 */
//@ ensures result == 0 &*& nodes(result, nil);
struct node *create_list()
{
    return 0;
}