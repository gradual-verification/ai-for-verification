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

// Helper lemma to add a node at the end of a list segment
lemma void lseg_add_tail(struct node *from, struct node *to, struct node *new_node)
    requires lseg(from, to) &*& to == 0 &*& malloc_block_node(new_node) &*& new_node->next |-> 0;
    ensures lseg(from, new_node) &*& new_node->next |-> 0;
{
    open lseg(from, to);
    if (from == to) {
        close lseg(new_node, 0);
    } else {
        lseg_add_tail(from->next, to, new_node);
        close lseg(from, new_node);
    }
}

// Helper lemma to traverse a list segment
lemma void lseg_traverse(struct node *from, struct node *to)
    requires lseg(from, to) &*& from != to;
    ensures lseg(from, from->next) &*& from->next |-> ?next &*& lseg(next, to);
{
    open lseg(from, to);
    if (from->next != to) {
        lseg_traverse(from->next, to);
    }
    close lseg(from->next, to);
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
        struct node *curr = head;
        //@ open llist(head);
        //@ open lseg(head, 0);
        
        while (curr->next != 0)
        //@ invariant curr != 0 &*& malloc_block_node(curr) &*& curr->next |-> ?next &*& lseg(next, 0);
        {
            //@ open lseg(curr->next, 0);
            struct node *tmp = curr;
            curr = curr->next;
            //@ close lseg(tmp->next, curr);
        }
        
        curr->next = new_node;
        //@ close lseg(new_node, 0);
        //@ lseg_add_tail(head, 0, new_node);
        //@ close llist(head);
        return head;
    }
}