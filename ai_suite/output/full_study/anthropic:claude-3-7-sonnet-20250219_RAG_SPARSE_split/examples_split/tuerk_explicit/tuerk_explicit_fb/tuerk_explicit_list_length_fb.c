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
int list_length(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *current = node;
    //@ open nodes(current, values);
    //@ close nodes(current, values);
    
    while (current != 0)
        /*@ invariant current == 0 ?
                      i == length(values) &*& nodes(node, values)
                    :
                      nodes(current, ?remaining) &*& nodes(node, ?prefix) &*&
                      values == append(prefix, remaining) &*&
                      i == length(prefix);
        @*/
    {
        //@ open nodes(current, remaining);
        current = current->next;
        i++;
        //@ close nodes(current, ?values0);
        //@ assert remaining == cons(?value, values0);
        //@ assert values == append(prefix, cons(value, values0));
        //@ assert i == length(prefix) + 1;
        //@ assert append(append(prefix, cons(value, nil)), values0) == append(prefix, cons(value, values0));
    }
    //@ open nodes(current, ?empty);
    //@ assert empty == nil;
    //@ assert values == append(prefix, empty);
    //@ assert i == length(prefix);
    //@ assert append(prefix, nil) == prefix;
    
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
        node->next |-> ?next &*& node->value |-> ?value &*& nodes(next, ?values0) &*& values == cons(value, values0);
@*/


// TODO: make this function pass the verification
int list_length(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *current = node;
    
    /*@
    // Create a ghost variable to track the remaining part of the list
    list<int> remaining = values;
    @*/
    
    while (current != 0)
        /*@ invariant nodes(current, remaining) &*& i + length(remaining) == length(values); @*/
    {
        //@ open nodes(current, remaining);
        current = current->next;
        i++;
        //@ remaining = tail(remaining);
        //@ close nodes(current, remaining);
    }
    
    //@ open nodes(current, remaining);
    //@ assert remaining == nil;
    //@ close nodes(current, remaining);
    
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
        node->next |-> ?next &*& node->value |-> ?value &*& nodes(next, ?values0) &*& values == cons(value, values0);
@*/


int list_length(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *current = node;
    
    /*@
    // Create a ghost variable to track the remaining part of the list
    list<int> remaining = values;
    @*/
    
    while (current != 0)
        //@ invariant current == 0 ? i == length(values) : nodes(current, remaining) &*& i + length(remaining) == length(values);
    {
        //@ open nodes(current, remaining);
        current = current->next;
        i++;
        //@ remaining = tail(remaining);
        //@ close nodes(current, remaining);
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
        node->next |-> ?next &*& node->value |-> ?value &*& nodes(next, ?values0) &*& values == cons(value, values0);
@*/


int list_length(struct node *node)
    //@ requires nodes(node, ?values);
    //@ ensures nodes(node, values) &*& result == length(values);
{
    int i = 0;
    struct node *current = node;
    
    /*@
    // Create a ghost variable to track the remaining part of the list
    list<int> remaining = values;
    @*/
    
    while (current != 0)
        //@ invariant nodes(current, remaining) &*& i + length(remaining) == length(values);
    {
        //@ open nodes(current, remaining);
        struct node *next = current->next;
        //@ assert current->value |-> ?value;
        i++;
        current = next;
        //@ assert remaining == cons(value, ?values0);
        //@ remaining = values0;
        //@ close nodes(current, remaining);
    }
    
    //@ assert current == 0;
    //@ open nodes(current, remaining);
    //@ assert remaining == nil;
    //@ close nodes(current, remaining);
    //@ assert i + length(remaining) == length(values);
    //@ assert i == length(values);
    
    return i;
}