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

lemma void lseg_append(struct node *p1, struct node *p2, struct node *p3)
    requires lseg(p1, p2) &*& lseg(p2, p3);
    ensures lseg(p1, p3);
{
    open lseg(p1, p2);
    if (p1 != p2) {
        lseg_append(p1->next, p2, p3);
        close lseg(p1, p3);
    }
}
@*/

// TODO: make this function pass the verification
struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close lseg(new_node, 0);

    if (head == 0) {
        //@ open llist(head);
        return new_node;
    } else {
        struct node *curr = head;
        //@ open llist(head);
        //@ close lseg(head, head);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& lseg(curr, 0) &*& lseg(new_node, 0);
        {
            //@ open lseg(curr, 0);
            struct node *tmp = curr;
            curr = curr->next;
            //@ close lseg(tmp, curr);
            //@ lseg_append(head, tmp, curr);
        }
        
        //@ open lseg(curr, 0);
        curr->next = new_node;
        //@ close lseg(curr, new_node);
        //@ lseg_append(head, curr, new_node);
        //@ lseg_append(head, new_node, 0);
        //@ close llist(head);
        return head;
    }
}