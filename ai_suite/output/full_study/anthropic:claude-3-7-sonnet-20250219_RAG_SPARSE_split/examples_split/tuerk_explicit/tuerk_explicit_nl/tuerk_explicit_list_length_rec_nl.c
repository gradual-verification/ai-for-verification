struct node {
    struct node *next;
    int value;
};

/*@
// Define a recursive predicate for a linked list
predicate lseg(struct node *from, struct node *to, int length) =
    from == to ?
        length == 0
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?value &*&
        malloc_block_node(from) &*&
        lseg(next, to, length - 1);

// Helper lemma to convert between lseg and list_length_rec
lemma int lseg_length(struct node *from, struct node *to)
    requires lseg(from, to, ?length);
    ensures lseg(from, to, length) &*& result == length;
{
    open lseg(from, to, length);
    if (from == to) {
        close lseg(from, to, length);
        return 0;
    } else {
        int length0 = lseg_length(from->next, to);
        close lseg(from, to, length);
        return 1 + length0;
    }
}
@*/

/***
 * Description:
The list_length_rec function calculates the length of a single linked list recursively.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
int list_length_rec(struct node *node)
    //@ requires lseg(node, 0, ?length);
    //@ ensures lseg(node, 0, length) &*& result == length;
{
    //@ open lseg(node, 0, length);
    if (node == 0) {
        //@ close lseg(0, 0, 0);
        return 0;
    } else {
        int length0 = list_length_rec(node->next);
        //@ close lseg(node, 0, length);
        return 1 + length0;
    }
}