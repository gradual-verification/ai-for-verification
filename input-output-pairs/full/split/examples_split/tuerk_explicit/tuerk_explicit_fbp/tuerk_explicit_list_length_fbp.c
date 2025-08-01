

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
int list_length(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
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

