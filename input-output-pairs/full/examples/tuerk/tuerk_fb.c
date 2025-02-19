struct node {
    struct node *next;
    int value;
};

/*@
predicate nodes(struct node *node; list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*& nodes(next, ?values0) &*& values == cons(value, values0);
@*/

int list_length_rec(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    if (node == 0)
        return 0;
    else {
        int length0 = list_length_rec(node->next);
        return 1 + length0;
    }
}

int list_length_iter(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    while (node != 0)
    {
        node = node->next;
        i++;
    }
    return i;
}
