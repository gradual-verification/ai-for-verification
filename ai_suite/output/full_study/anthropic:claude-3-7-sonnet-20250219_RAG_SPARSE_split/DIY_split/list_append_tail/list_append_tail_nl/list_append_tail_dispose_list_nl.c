#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate nodes(struct node *n; list<struct node *> values) =
    n == 0 ?
        values == nil
    :
        n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?values0) &*&
        values == cons(n, values0);
@*/

/***
 * Description:
 * The `dispose_list` function disposes a given list.
 *
 * @param head: the head of a given list
 * It makes sure that the given list is freed. 
 */
void dispose_list(struct node *head)
    //@ requires nodes(head, ?values);
    //@ ensures true;
{
    if (head != 0) {
        //@ open nodes(head, values);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open nodes(head, values);
    }
}