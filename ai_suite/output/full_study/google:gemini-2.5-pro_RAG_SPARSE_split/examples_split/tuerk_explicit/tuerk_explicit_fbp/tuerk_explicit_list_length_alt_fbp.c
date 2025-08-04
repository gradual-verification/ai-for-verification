#include <limits.h>

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

predicate lseg(struct node *first, struct node *last, list<int> values) =
    first == last ?
        values == nil
    :
        first != 0 &*&
        first->next |-> ?next &*& first->value |-> ?value &*& malloc_block_node(first) &*&
        lseg(next, last, ?values0) &*& values == cons(value, values0);

lemma void nodes_to_lseg(struct node *n)
    requires nodes(n, ?values);
    ensures lseg(n, 0, values);
{
    open nodes(n, values);
    if (n != 0) {
        nodes_to_lseg(n->next);
        close lseg(n, 0, values);
    } else {
        close lseg(0, 0, nil);
    }
}

lemma void lseg_to_nodes(struct node *n)
    requires lseg(n, 0, ?values);
    ensures nodes(n, values);
{
    open lseg(n, 0, values);
    if (n != 0) {
        lseg_to_nodes(n->next);
        close nodes(n, values);
    } else {
        close nodes(0, nil);
    }
}

lemma void lseg_append_node(struct node *first)
    requires lseg(first, ?last, ?vs1) &*& last != 0 &*&
             last->value |-> ?v &*& last->next |-> ?next &*& malloc_block_node(last) &*&
             lseg(next, 0, ?vs2);
    ensures lseg(first, next, append(vs1, cons(v, nil))) &*& lseg(next, 0, vs2);
{
    open lseg(first, last, vs1);
    if (first != last) {
        lseg_append_node(first->next);
    }
    close lseg(first, next, append(vs1, cons(v, nil)));
}

@*/


// TODO: make this function pass the verification
int list_length_alt(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    //@ struct node *initial_node = node;
    //@ nodes_to_lseg(initial_node);
    int i;
    //@ close lseg(initial_node, initial_node, nil);
    for (i = 0; node != 0; node = node->next, i++)
        /*@
        invariant lseg(initial_node, node, ?values0) &*& lseg(node, 0, ?values1) &*&
                  values == append(values0, values1) &*& i == length(values0);
        @*/
    {
        //@ open lseg(node, 0, values1);
        //@ lseg_append_node(initial_node);
        //@ append_assoc(values0, cons(head(values1), nil), tail(values1));
    }
    //@ open lseg(0, 0, _);
    //@ lseg_to_nodes(initial_node);
    return i;
}