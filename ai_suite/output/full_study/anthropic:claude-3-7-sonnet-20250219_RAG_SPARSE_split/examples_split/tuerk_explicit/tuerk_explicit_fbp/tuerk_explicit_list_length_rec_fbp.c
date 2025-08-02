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


// TODO: make this function pass the verification
int list_length_rec(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    if (node == 0) {
        //@ open nodes(node, values);
        //@ close nodes(node, values);
        return 0;
    } else {
        //@ open nodes(node, values);
        //@ assert node->next |-> ?next;
        //@ assert nodes(next, ?values0);
        //@ assert values == cons(?value, values0);
        //@ assert length(values) == 1 + length(values0);
        //@ assert length(values0) <= INT_MAX - 1;
        int length0 = list_length_rec(node->next);
        //@ assert length0 == length(values0);
        //@ close nodes(node, values);
        return 1 + length0;
    }
}