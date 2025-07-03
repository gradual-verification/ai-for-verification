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

lemma void lseg_add(struct node *n)
    requires lseg(n, ?end) &*& n != 0 &*& n->next |-> ?next &*& malloc_block_node(n) &*& lseg(next, end);
    ensures lseg(n, end);
{
    open lseg(n, end);
    if (n != end) {
        lseg_add(next);
    }
    close lseg(n, end);
}
@*/

struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close lseg(new_node, 0);

    if (head == 0) {
        //@ open lseg(0, 0);
        return new_node;
    } else {
        struct node *curr = head;
        //@ open lseg(head, 0);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& curr != 0 &*& curr->next |-> ?next &*& malloc_block_node(curr) &*& lseg(next, 0);
        {
            //@ struct node *next = curr->next;
            //@ open lseg(next, 0);
            curr = curr->next;
            //@ close lseg(curr, curr);
            //@ lseg_add(head);
        }
        //@ open lseg(0, 0);
        curr->next = new_node;
        //@ close lseg(new_node, 0);
        //@ lseg_add(head);
        return head;
    }
}