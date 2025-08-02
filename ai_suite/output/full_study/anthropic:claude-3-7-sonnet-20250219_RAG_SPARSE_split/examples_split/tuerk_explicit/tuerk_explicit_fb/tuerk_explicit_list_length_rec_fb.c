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
int list_length_rec(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    if (node == 0) {
        //@ close nodes(node, nil);
        return 0;
    } else {
        //@ open nodes(node, values);
        int length0 = list_length_rec(node->next);
        //@ assert node->next |-> ?next;
        //@ assert node->value |-> ?value;
        //@ assert nodes(next, ?values0);
        //@ assert values == cons(value, values0);
        //@ assert length0 == length(values0);
        //@ close nodes(node, values);
        return 1 + length0;
    }
}