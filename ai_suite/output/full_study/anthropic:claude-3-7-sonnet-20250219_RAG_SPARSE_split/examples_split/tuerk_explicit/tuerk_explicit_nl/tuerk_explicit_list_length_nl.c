struct node {
    struct node *next;
    int value;
};

/*@
// Define a recursive predicate for a linked list segment
predicate lseg(struct node *from, struct node *to, int length) =
    from == to ?
        length == 0
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?value &*&
        malloc_block_node(from) &*&
        lseg(next, to, length - 1);

// Define a lemma to convert lseg to a different form
lemma void lseg_to_length_lemma(struct node *from, struct node *to)
    requires lseg(from, to, ?length);
    ensures lseg(from, to, length) &*& (from == to ? length == 0 : length > 0);
{
    open lseg(from, to, length);
    if (from != to) {
        lseg_to_length_lemma(from->next, to);
    }
    close lseg(from, to, length);
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_length function calculates the length of a single linked list iteratively by traversing it in a while loop.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
/*@
requires lseg(node, 0, ?length);
ensures lseg(node, 0, length) &*& result == length;
@*/
int list_length(struct node *node)
{
    int i = 0;
    struct node *current = node;
    //@ open lseg(node, 0, length);
    //@ if (node == 0) { close lseg(0, 0, 0); }
    
    while (current != 0)
    /*@
        invariant lseg(current, 0, ?remaining) &*& 
                 (node == 0 ? current == 0 &*& i == 0 &*& remaining == 0 : 
                             lseg(node, current, i) &*& length == i + remaining);
    @*/
    {
        //@ open lseg(current, 0, remaining);
        current = current->next;
        i++;
        //@ close lseg(node, current, i);
    }
    //@ open lseg(current, 0, _);
    //@ close lseg(0, 0, 0);
    //@ close lseg(node, 0, length);
    return i;
}