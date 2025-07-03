#include <stdlib.h>

struct node {
    struct node *next;
};

/*@
predicate lseg(struct node *from, struct node *to) =
    from == to ?
        true
    :
        from != 0 &*&
        malloc_block_node(from) &*&
        from->next |-> ?next &*&
        lseg(next, to);

predicate llist(struct node *head) =
    lseg(head, 0);
@*/

/*@
lemma void lseg_append(struct node *first, struct node *last)
    requires
        lseg(first, last) &*&
        last != 0 &*&
        last->next |-> ?next &*&
        malloc_block_node(last) &*&
        lseg(next, 0);
    ensures
        lseg(first, next) &*&
        lseg(next, 0);
{
    open lseg(first, last);
    if (first == last) {
        // we are at the last node: close the extended segment
        close lseg(first, next);
    } else {
        lseg_append(first->next, last);
        close lseg(first, next);
    }
}
@*/

/*@
/* Recursive helper: attaches the list that starts in new_node to the
   end of the list that starts in head and returns the (unchanged) head
   of the resulting list. */
static struct node *append_tail_rec(struct node *head, struct node *new_node)
    //@ requires llist(head) &*& lseg(new_node, 0);
    //@ ensures  llist(result);
{
    if (head == 0) {
        // The original list is empty: the new node is the new list.
        return new_node;
    } else {
        //@ open lseg(head, 0);
        struct node *next = head->next;
        struct node *tail = append_tail_rec(next, new_node);
        head->next = tail;
        //@ close lseg(head, 0);
        return head;
    }
}
@*/

// TODO: make this function pass the verification
struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures  llist(result);
{
    /* allocate and initialise the new last node */
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    /* Build the predicate describing the freshly allocated single node
       so we can pass it to the recursive helper. */
    //@ close lseg(0, 0);
    //@ close malloc_block_node(new_node);
    //@ close lseg(new_node, 0);

    /* delegate to the recursively verified helper */
    struct node *res = append_tail_rec(head, new_node);
    return res;
}