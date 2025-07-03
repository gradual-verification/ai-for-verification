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
struct node *create_list()
    //@ requires true;
    //@ ensures llist(result);
{
    /*  An empty list is represented by the null pointer.
        To satisfy the post-condition we have to establish
        llist(0), i.e. lseg(0,0).  */
    //@ close lseg(0, 0);
    //@ close llist(0);
    return 0;
}