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
@*/

// TODO: make this function pass the verification
struct node *append_tail(struct node *head)
    //@ requires llist(head);
    //@ ensures llist(result);
{
    struct node *new_node = malloc(sizeof(struct node));
    //@ if (new_node == 0) abort();
    if (new_node == 0) abort();
    new_node->next = 0;
    //@ close lseg(new_node, 0);

    if (head == 0) {
        //@ close llist(new_node);
        return new_node;
    } else {
        //@ open llist(head);
        struct node *curr = head;
        
        /*@
        // Define a lemma to help with the loop invariant
        lemma void lseg_add_to_end(struct node *from, struct node *to)
            requires lseg(from, to) &*& lseg(to, 0);
            ensures lseg(from, 0);
        {
            open lseg(from, to);
            if (from == to) {
                // Base case: from == to
            } else {
                // Recursive case
                lseg_add_to_end(from->next, to);
                close lseg(from, 0);
            }
        }
        @*/
        
        //@ lseg_add_to_end(head, 0);
        
        while (curr->next != 0)
            //@ invariant curr != 0 &*& curr->next |-> ?next &*& lseg(head, curr) &*& lseg(next, 0);
        {
            //@ open lseg(next, 0);
            struct node *tmp = curr;
            curr = curr->next;
            //@ close lseg(tmp, curr);
        }
        
        curr->next = new_node;
        //@ close lseg(curr, 0);
        //@ lseg_add_to_end(head, curr);
        //@ close llist(head);
        return head;
    }
}