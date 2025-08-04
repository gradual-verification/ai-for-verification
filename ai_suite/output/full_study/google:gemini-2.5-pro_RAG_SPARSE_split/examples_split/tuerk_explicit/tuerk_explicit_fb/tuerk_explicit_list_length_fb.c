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

predicate lseg(struct node *first, struct node *last, list<int> values) =
    first == last ?
        values == nil
    :
        first->next |-> ?next &*& first->value |-> ?value &*&
        lseg(next, last, ?values0) &*& values == cons(value, values0);

lemma void nodes_to_lseg(struct node *n)
    requires nodes(n, ?values);
    ensures lseg(n, 0, values);
{
    open nodes(n, values);
    if (n != 0) {
        nodes_to_lseg(n->next);
    }
    close lseg(n, 0, values);
}

lemma void lseg_to_nodes(struct node *n)
    requires lseg(n, 0, ?values);
    ensures nodes(n, values);
{
    open lseg(n, 0, values);
    if (n != 0) {
        lseg_to_nodes(n->next);
    }
    close nodes(n, values);
}

lemma void lseg_add(struct node *first)
    requires lseg(first, ?last, ?vs1) &*& last != 0 &*&
             last->next |-> ?next &*& last->value |-> ?val &*&
             lseg(next, 0, ?vs2);
    ensures lseg(first, next, append(vs1, cons(val, nil))) &*& lseg(next, 0, vs2);
{
    open lseg(first, last, vs1);
    if (first != last) {
        lseg_add(first->next);
    }
    // The open/close below helps VeriFast deduce that 'first' and 'next' are distinct,
    // which is required to close the lseg predicate when its value list is not nil.
    open lseg(next, 0, vs2);
    close lseg(next, 0, vs2);
    close lseg(first, next, append(vs1, cons(val, nil)));
}

@*/


// TODO: make this function pass the verification
int list_length(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    struct node *head = node;
    //@ nodes_to_lseg(head);
    int i = 0;
    //@ close lseg(head, head, nil);
    while (node != 0)
        /*@
        invariant lseg(head, node, ?visited_values) &*& lseg(node, 0, ?remaining_values) &*&
                  values == append(visited_values, remaining_values) &*&
                  i == length(visited_values);
        @*/
    {
        //@ open lseg(node, 0, remaining_values);
        struct node *next_node = node->next;
        i++;
        //@ lseg_add(head);
        node = next_node;
    }
    //@ open lseg(0, 0, _); // This proves remaining_values is nil.
    //@ lseg_to_nodes(head);
    return i;
}