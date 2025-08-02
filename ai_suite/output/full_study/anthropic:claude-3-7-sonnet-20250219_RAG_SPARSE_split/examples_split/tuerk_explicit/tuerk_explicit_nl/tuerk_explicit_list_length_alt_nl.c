struct node {
    struct node *next;
    int value;
};

//@ #include "prelude.gh"

/*@
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        node->next |-> ?next &*& node->value |-> ?value &*&
        malloc_block_node(node) &*& nodes(next, count - 1);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The list_length_alt function calculates the length of a single linked list iteratively by traversing it in a for loop.

@param node: the starting node of the linkedlist

This function makes sure that the linked list is not changed, and the return valie is the length of it.
*/
int list_length_alt(struct node *node)
//@ requires nodes(node, ?count);
//@ ensures nodes(node, count) &*& result == count;
{
    int i;
    //@ open nodes(node, count);
    //@ close nodes(node, count);
    
    //@ assert node == 0 ? count == 0 : true;
    
    //@ if (node == 0) {
    //@   close nodes(node, 0);
    //@ }
    
    for (i = 0; node != 0; node = node->next, i++)
        /*@ invariant node == 0 ? 
                      i == count &*& nodes(node, 0) 
                    : 
                      nodes(node, count - i) &*& i >= 0 &*& i <= count; 
        @*/
    {
        //@ open nodes(node, count - i);
        //@ assert node->next |-> ?next;
        //@ assert nodes(next, (count - i) - 1);
        //@ close nodes(next, count - (i + 1));
    }
    
    //@ open nodes(0, 0);
    return i;
}