#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*& from->next |-> ?next &*&
        lseg(next, to);

predicate llist(struct node *head) =
    lseg(head, 0);

lemma void lseg_append(struct node *first, struct node *last)
    requires lseg(first, last) &*& last != 0 &*& last->next |-> ?next;
    ensures lseg(first, next);
{
    open lseg(first, last);
    if (first != last) {
        lseg_append(first->next, last);
    }
}

lemma void lseg_join(struct node *n1)
    requires lseg(n1, ?n2) &*& lseg(n2, ?n3);
    ensures lseg(n1, n3);
{
    open lseg(n1, n2);
    if (n1 != n2) {
        lseg_join(n1->next);
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
        struct node *curr = head;
        //@ close lseg(head, head);
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& llist(curr) &*& curr != 0;
        {
            //@ open llist(curr);
            struct node *tmp = curr;
            curr = curr->next;
            //@ lseg_append(head, tmp);
        }
        //@ open llist(curr);
        curr->next = new_node;
        //@ lseg_append(head, curr);
        //@ lseg_join(head);
        return head;
    }
}