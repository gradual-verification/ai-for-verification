struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, ?values0) &*& values == cons(value, values0);
@*/


int list_length_alt(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i;
    //@ open nodes(node, values);
    for (i = 0; node != 0; node = node->next, i++)
        /*@ invariant (node == 0 ? 
                        values == nil &*& i == 0 : 
                        node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& 
                        nodes(next, ?values0) &*& values == cons(value, values0)) &*&
                     i == length(values) - length(node == 0 ? nil : cons(head(values), values0)); @*/
    {
        //@ assert node != 0;
        //@ assert node->next |-> ?next;
        //@ assert node->value |-> ?value;
        //@ assert malloc_block_node(node);
        //@ assert nodes(next, ?values0);
        //@ assert values == cons(value, values0);
        
        //@ open nodes(next, values0);
        //@ close nodes(next, values0);
    }
    //@ close nodes(node, values);
    return i;
}