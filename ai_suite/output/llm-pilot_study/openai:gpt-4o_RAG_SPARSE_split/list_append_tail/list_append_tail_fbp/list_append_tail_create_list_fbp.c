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
    //@ close lseg(0, 0);
    //@ close llist(0);
    return 0;
}