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

lemma void lseg_add(struct node *from, struct node *to)
    requires lseg(from, to) &*& to != 0 &*& to->next |-> ?next &*& malloc_block_node(to);
    ensures lseg(from, next);
{
    open lseg(from, to);
    if (from == to) {
        // Close lseg(to, next) using the current node
        close lseg(next, next);  // Base case for next segment
        close lseg(to, next);    // Recursive case for current node
    } else {
        // Recursively extend the segment
        struct node *n = from->next;
        lseg_add(n, to);
        close lseg(from, next);
    }
}
@*/

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
        //@ close lseg(head, head);  // Initialize segment from head to head (empty)
        //@ open llist(head);
        while (curr->next != 0)
            /*@ invariant lseg(head, curr) &*& lseg(curr, 0); @*/
        {
            //@ open lseg(curr, 0);  // Unpack current segment
            struct node *tmp = curr;
            curr = curr->next;
            //@ lseg_add(head, tmp);  // Extend head segment to include tmp
        }
        //@ open lseg(curr, 0);  // Unpack last segment (curr->next must be 0)
        curr->next = new_node;
        //@ close lseg(0, 0);       // Close segment for new_node's next (null)
        //@ close lseg(new_node, 0); // Close segment for new_node
        //@ close lseg(curr, 0);    // Close segment for curr (now points to new_node)
        //@ close llist(head);      // Reconstruct full list
        return head;
    }
}