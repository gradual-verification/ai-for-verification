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

// Lemma to convert a linked list to a linked list segment
/*@
lemma void llist_to_lseg(struct node *head)
    requires llist(head);
    ensures lseg(head, 0);
{
    open llist(head);
}
@*/

// Lemma to convert a linked list segment to a linked list
/*@
lemma void lseg_to_llist(struct node *head)
    requires lseg(head, 0);
    ensures llist(head);
{
    close llist(head);
}
@*/

// Lemma to append a node to a linked list segment
/*@
lemma void lseg_append(struct node *from, struct node *to, struct node *new_node)
    requires lseg(from, to) &*& new_node->next |-> 0 &*& malloc_block_node(new_node);
    ensures lseg(from, new_node) &*& new_node->next |-> 0;
{
    open lseg(from, to);
    if (from != to) {
        lseg_append(from->next, to, new_node);
    }
    close lseg(from, new_node);
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

    if (head == 0) {
        //@ close llist(new_node);
        return new_node;
    } else {
        //@ llist_to_lseg(head);
        struct node *curr = head;
        while (curr->next != 0)
            //@ invariant lseg(head, curr) &*& curr->next |-> ?next &*& lseg(next, 0);
        {
            //@ open lseg(curr, 0);
            curr = curr->next;
        }
        //@ open lseg(curr, 0);
        curr->next = new_node;
        //@ lseg_append(head, curr, new_node);
        //@ lseg_to_llist(head);
        return head;
    }
}