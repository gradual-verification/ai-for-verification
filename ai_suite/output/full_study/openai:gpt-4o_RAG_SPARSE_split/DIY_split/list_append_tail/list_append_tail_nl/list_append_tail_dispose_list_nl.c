#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate nodes(struct node *n) =
    n == 0 ? true : n->next |-> ?next &*& malloc_block(n, sizeof(struct node)) &*& nodes(next);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_list` function disposes a given list.
 *
 * @param head: the head of a given list
 * It makes sure that the given list is freed. 
 */
//@ requires nodes(head);
//@ ensures true;
void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    }
}