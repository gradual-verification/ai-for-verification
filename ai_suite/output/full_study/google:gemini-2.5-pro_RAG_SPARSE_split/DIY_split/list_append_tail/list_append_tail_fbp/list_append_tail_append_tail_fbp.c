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

lemma void lseg_append(struct node *p)
    requires lseg(p, ?q) &*& q != 0 &*& malloc_block_node(q) &*& q->next |-> ?r &*& lseg(r, 0);
    ensures lseg(p, r) &*& lseg(r, 0);
{
    open lseg(p, q);
    if (p == q) {
        close lseg(p, r);
    } else {
        lseg_append(p->next);
        close lseg(p, r);
    }
}

lemma void lseg_chain(struct node *p, struct node *q, struct node *r)
    requires lseg(p, q) &*& lseg(q, r);
    ensures lseg(p, r);
{
    open lseg(p, q);
    if (p != q) {
        lseg_chain(p->next, q, r);
        close lseg(p, r);
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
    //@ close llist(new_node);

    if (head == 0) {
        return new_node;
    } else {
        //@ open llist(head);
        struct node *curr = head;
        //@ close lseg(head, head);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& lseg(curr, 0);
        {
            //@ open lseg(curr, 0);
            lseg_append(head);
            struct node *tmp = curr;
            curr = curr->next;
        }
        
        //@ open lseg(curr, 0);
        //@ open llist(new_node);
        curr->next = new_node;
        //@ close lseg(curr, 0);
        
        lseg_chain(head, curr, 0);
        
        return head;
    }
}