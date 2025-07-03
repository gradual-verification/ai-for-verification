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

lemma void lseg_add(struct node *first)
    requires lseg(first, ?last) &*& last != 0 &*& last->next |-> ?next &*& malloc_block_node(last) &*& lseg(next, ?end);
    ensures lseg(first, next) &*& lseg(next, end);
{
    open lseg(first, last);
    if (first == last) {
        close lseg(next, next);
    } else {
        lseg_add(first->next);
    }
    open lseg(next, end);
    close lseg(next, end);
    close lseg(first, next);
}
@*/

void dispose_list(struct node *head)
    //@ requires llist(head);
    //@ ensures true;
{
    if (head != 0) {
        //@ open llist(head);
        //@ open lseg(head, 0);
        struct node *next = head->next;
        dispose_list(next);
        free(head);
    } else {
        //@ open llist(head);
        //@ open lseg(head, 0);
    }
}