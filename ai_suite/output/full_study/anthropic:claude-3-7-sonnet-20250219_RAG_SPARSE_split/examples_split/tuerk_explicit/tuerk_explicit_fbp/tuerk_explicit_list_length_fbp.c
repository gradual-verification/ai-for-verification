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


int list_length(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *current = node;
    //@ open nodes(node, values);
    //@ close nodes(node, values);
    
    while (current != 0)
        /*@ invariant 
            current == 0 ? 
                nodes(node, values) &*& i == length(values)
            : 
                current |-> ?next &*& current->value |-> ?value &*& malloc_block_node(current) &*& 
                nodes(next, ?values0) &*& 
                nodes(node, values) == current->next |-> next &*& current->value |-> value &*& 
                malloc_block_node(current) &*& nodes(next, values0) &*& 
                i + length(values0) + 1 == length(values);
        @*/
    {
        //@ open nodes(current, ?current_values);
        current = current->next;
        i++;
        //@ assert i + length(current_values) == length(values);
    }
    return i;
}
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


int list_length(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *current = node;
    
    //@ list<int> remaining_values = values;
    
    while (current != 0)
        /*@ invariant 
            nodes(current, ?curr_values) &*& 
            i + length(curr_values) == length(values) &*&
            i <= INT_MAX;
        @*/
    {
        //@ open nodes(current, curr_values);
        current = current->next;
        i++;
        //@ close nodes(current, tail(curr_values));
    }
    //@ open nodes(current, _);
    //@ close nodes(current, nil);
    return i;
}
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


int list_length(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *n = node;
    
    /*@
    predicate nodes_segment(struct node *start, struct node *current, list<int> processed, list<int> remaining) =
        nodes(current, remaining) &*& 
        length(processed) == i &*&
        append(processed, remaining) == values;
    @*/
    
    //@ close nodes_segment(node, node, nil, values);
    
    while (n != 0)
        //@ invariant nodes_segment(node, n, ?processed, ?remaining) &*& i <= INT_MAX;
    {
        //@ open nodes_segment(node, n, processed, remaining);
        //@ open nodes(n, remaining);
        n = n->next;
        i++;
        //@ close nodes(n, tail(remaining));
        //@ close nodes_segment(node, n, append(processed, cons(head(remaining), nil)), tail(remaining));
    }
    
    //@ open nodes_segment(node, n, ?final_processed, ?final_remaining);
    //@ assert final_remaining == nil;
    //@ assert append(final_processed, nil) == values;
    //@ assert length(final_processed) == i;
    //@ assert length(values) == i;
    
    return i;
}
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


int list_length(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *n = node;
    
    /*@
    lemma void nodes_split(struct node *start, struct node *current)
        requires nodes(start, ?vs) &*& start != 0;
        ensures start->next |-> ?next &*& start->value |-> ?value &*& malloc_block_node(start) &*& nodes(next, ?vs0) &*& vs == cons(value, vs0);
    {
        open nodes(start, vs);
    }
    @*/
    
    while (n != 0)
        /*@ invariant 
            n == 0 ? 
                nodes(n, nil) &*& i == length(values)
            : 
                nodes(n, ?remaining) &*& i + length(remaining) == length(values);
        @*/
    {
        //@ if (n != 0) nodes_split(n, n);
        //@ open nodes(n, _);
        n = n->next;
        i++;
        //@ close nodes(n, ?remaining);
    }
    
    return i;
}
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


int list_length(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *n = node;
    
    //@ list<int> remaining = values;
    
    while (n != 0)
        //@ invariant nodes(n, remaining) &*& i + length(remaining) == length(values);
    {
        //@ open nodes(n, remaining);
        n = n->next;
        i++;
        //@ remaining = tail(remaining);
        //@ close nodes(n, remaining);
    }
    
    //@ assert remaining == nil;
    //@ assert i == length(values);
    
    return i;
}