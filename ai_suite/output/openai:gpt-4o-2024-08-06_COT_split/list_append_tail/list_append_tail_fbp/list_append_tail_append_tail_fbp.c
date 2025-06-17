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

// TODO: make this function pass the verification
struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    //@ open llist(head);
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close lseg(new_node, 0);
    //@ close llist(new_node);

    if (head == 0) {
        return new_node;
    } else {
        struct node *curr = head;
        //@ open lseg(head, 0);
        while (curr->next != 0)
        //@ invariant lseg(head, curr) &*& curr != 0 &*& malloc_block_node(curr) &*& curr->next |-> ?next &*& lseg(next, 0);
        {
            struct node *tmp = curr;
            curr = curr->next;
            //@ open lseg(curr, 0);
            //@ close lseg(tmp, curr);
        }
        curr->next = new_node;
        //@ close lseg(curr, 0);
        //@ close llist(head);
        return head;
    }
}