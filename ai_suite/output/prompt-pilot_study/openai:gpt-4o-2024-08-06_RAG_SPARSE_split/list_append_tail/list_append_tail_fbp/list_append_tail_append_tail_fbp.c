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

lemma void lseg_to_llist(struct node *from)
    requires lseg(from, 0);
    ensures llist(from);
{
    open lseg(from, 0);
    if (from != 0) {
        lseg_to_llist(from->next);
    }
    close llist(from);
}

lemma void llist_to_lseg(struct node *from)
    requires llist(from);
    ensures lseg(from, 0);
{
    open llist(from);
    if (from != 0) {
        llist_to_lseg(from->next);
    }
    close lseg(from, 0);
}

lemma void lseg_append(struct node *from, struct node *to)
    requires lseg(from, to) &*& to != 0 &*& malloc_block_node(to) &*& to->next |-> ?next &*& lseg(next, 0);
    ensures lseg(from, 0);
{
    open lseg(from, to);
    if (from != to) {
        lseg_append(from->next, to);
    }
    close lseg(from, 0);
}

// TODO: make this function pass the verification
struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        return new_node;
    } else {
        struct node *curr = head;
        //@ llist_to_lseg(head);
        while (curr->next != 0)
        //@ invariant lseg(head, curr) &*& curr != 0 &*& malloc_block_node(curr) &*& curr->next |-> ?next &*& lseg(next, 0);
        {
            //@ open lseg(curr, 0);
            curr = curr->next;
        }
        curr->next = new_node;
        //@ lseg_append(head, curr);
        //@ lseg_to_llist(head);
        return head;
    }
}