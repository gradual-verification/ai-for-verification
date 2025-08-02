struct node {
    struct node *next;
    int value;
};

/*@

predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& nodes(next, ?values0) &*& values == cons(value, values0);
@*/


// TODO: make this function pass the verification
int list_length_alt(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i;
    struct node *current = node;
    //@ open nodes(current, values);
    //@ close nodes(current, values);
    for (i = 0; node != 0; node = node->next, i++)
        /*@ invariant nodes(node, ?remaining) &*& nodes(current, values) &*& 
                     i == length(values) - length(remaining); @*/
    {
        //@ open nodes(node, remaining);
        //@ assert node->next |-> ?next;
        //@ assert node->value |-> ?value;
        //@ assert nodes(next, ?values0);
        //@ assert remaining == cons(value, values0);
        //@ close nodes(next, values0);
    }
    //@ assert node == 0;
    //@ assert i == length(values);
    return i;
}