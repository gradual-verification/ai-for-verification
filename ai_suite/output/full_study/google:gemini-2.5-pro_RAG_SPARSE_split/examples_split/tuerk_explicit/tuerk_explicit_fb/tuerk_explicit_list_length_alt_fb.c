#include <stdlib.h>

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

predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        from != 0 &*&
        from->next |-> ?next &*& from->value |-> ?value &*&
        lseg(next, to, ?values0) &*& values == cons(value, values0);

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

lemma void lseg_append(struct node *first)
    requires lseg(first, ?last, ?vs1) &*& last != 0 &*& last->next |-> ?next &*& last->value |-> ?v &*& lseg(next, 0, ?vs2);
    ensures lseg(first, next, append(vs1, cons(v, nil))) &*& lseg(next, 0, vs2);
{
    open lseg(first, last, vs1);
    if (first != last) {
        lseg_append(first->next);
    }
    close lseg(first, next, append(vs1, cons(v, nil)));
}

@*/


// TODO: make this function pass the verification
int list_length_alt(struct node *head)
    //@ requires nodes(head, ?values);
    //@ ensures nodes(head, values) &*& result == length(values);
{
    //@ nodes_to_lseg(head);
    struct node *node = head;
    int i;
    //@ close lseg(head, head, nil);
    for (i = 0; node != 0; node = node->next, i++)
        /*@
        invariant
            lseg(head, node, ?traversed_values) &*&
            lseg(node, 0, ?remaining_values) &*&
            values == append(traversed_values, remaining_values) &*&
            i == length(traversed_values);
        @*/
    {
        //@ open lseg(node, 0, remaining_values);
        //@ lseg_append(head);
        //@ append_assoc(traversed_values, cons(node->value, nil), tail(remaining_values));
    }
    //@ open lseg(node, 0, remaining_values);
    //@ lseg_to_nodes(head);
    return i;
}