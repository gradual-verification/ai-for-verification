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

predicate lseg(struct node *from, struct node *to, list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        from->next |-> ?next &*& from->value |-> ?v &*& malloc_block_node(from) &*&
        lseg(next, to, ?vs_tail) &*& vs == cons(v, vs_tail);

lemma void nodes_to_lseg(struct node *n)
    requires nodes(n, ?vs);
    ensures lseg(n, 0, vs);
{
    open nodes(n, vs);
    if (n != 0) {
        nodes_to_lseg(n->next);
    }
    close lseg(n, 0, vs);
}

lemma void lseg_to_nodes(struct node *n)
    requires lseg(n, 0, ?vs);
    ensures nodes(n, vs);
{
    open lseg(n, 0, vs);
    if (n != 0) {
        lseg_to_nodes(n->next);
    }
    close nodes(n, vs);
}

lemma void lseg_move_one(struct node *h, struct node *c)
    requires lseg(h, c, ?vs1) &*& c != 0 &*& c->next |-> ?n &*& c->value |-> ?v &*& malloc_block_node(c);
    ensures lseg(h, n, append(vs1, cons(v, nil)));
{
    open lseg(h, c, vs1);
    if (h != c) {
        lseg_move_one(h->next, c);
    }
    close lseg(h, n, append(vs1, cons(v, nil)));
}

@*/


// TODO: make this function pass the verification
int list_length(struct node *node)
    //@ requires nodes(node, ?values) &*& length(values) <= INT_MAX;
    //@ ensures nodes(node, values) &*& result == length(values);
{
    struct node *head = node;
    //@ nodes_to_lseg(head);
    int i = 0;
    //@ close lseg(head, node, nil);
    while (node != 0)
        /*@
        invariant lseg(head, node, ?traversed_vs) &*& lseg(node, 0, ?remaining_vs) &*&
                  values == append(traversed_vs, remaining_vs) &*&
                  i == length(traversed_vs);
        @*/
    {
        //@ open lseg(node, 0, remaining_vs);
        struct node *next = node->next;
        //@ int v = node->value;
        //@ lseg_move_one(head, node);
        //@ append_assoc(traversed_vs, cons(v, nil), tail(remaining_vs));
        node = next;
        i++;
    }
    //@ open lseg(0, 0, _);
    //@ lseg_to_nodes(head);
    return i;
}