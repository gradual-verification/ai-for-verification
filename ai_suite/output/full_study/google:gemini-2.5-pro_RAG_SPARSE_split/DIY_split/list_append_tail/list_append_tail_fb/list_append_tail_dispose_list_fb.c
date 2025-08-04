#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*& from->next |-> ?next &*& malloc_block_node(from) &*&
        lseg(next, to);

predicate llist(struct node *head) =
    lseg(head, 0);
@*/

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    //@ open llist(head);
    if (head != 0) {
        //@ open lseg(head, 0);
        dispose_list(head->next);
        free(head);
    } else {
        //@ open lseg(0, 0);
    }
}