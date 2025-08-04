#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate list(struct node *n) =
    n == 0 ?
        true
    :
        n->next |-> ?next &*&
        malloc_block_node(n) &*&
        list(next);
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `dispose_list` function disposes a given list.
 *
 * @param head: the head of a given list
 * It makes sure that the given list is freed. 
 */
void dispose_list(struct node *head)
    //@ requires list(head);
    //@ ensures true;
{
    //@ open list(head);
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    } else {
    }
}