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
    if (new_node == 0) abort();
    new_node->next = 0;
    
    //@ close lseg(new_node, 0);
    //@ close llist(new_node);

    if (head == 0) {
        return new_node;
    } else {
        //@ open llist(head);
        //@ open lseg(head, 0);
        
        struct node *curr = head;
        
        /*@
        lemma void lseg_add_tail(struct node *from, struct node *to)
            requires lseg(from, to) &*& lseg(to, 0);
            ensures lseg(from, 0);
        {
            open lseg(from, to);
            if (from == to) {
                open lseg(to, 0);
                close lseg(from, 0);
            } else {
                lseg_add_tail(from->next, to);
                close lseg(from, 0);
            }
        }
        @*/
        
        //@ close lseg(curr, curr);
        while (curr->next != 0)
            //@ invariant curr != 0 &*& curr->next |-> ?next &*& malloc_block_node(curr) &*& lseg(next, 0) &*& lseg(head, curr);
        {
            struct node *tmp = curr;
            //@ open lseg(curr->next, 0);
            curr = curr->next;
            //@ close lseg(tmp, curr);
            //@ lseg_add_tail(head, tmp);
        }
        
        curr->next = new_node;
        //@ lseg_add_tail(head, curr);
        
        return head;
    }
}