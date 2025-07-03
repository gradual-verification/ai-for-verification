#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*& malloc_block_node(from) &*& from->next |-> ?next &*&
        lseg(next, to);

predicate llist(struct node *head) =
    lseg(head, 0);
@*/

// verified implementation
void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    //@ open llist(head);          // reveal the list segment
    //@ open lseg(head, 0);        // obtain the first node (if any)

    if (head != 0) {
        dispose_list(head->next);  // recursively dispose the tail
        free(head);                // free the current node
    } else {
        // empty list – nothing to free
    }
}