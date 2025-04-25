#include "stdlib.h"

struct node {
    struct node *next;
};

/*@

predicate list(struct node *node) =
    node == 0 ? true :node->next |-> ?next &*& malloc_block_node(node) &*& list(next);

@*/

/*@
predicate lseg(struct node *first, struct node *last) =
    first == last ?
        true
    :
        first != 0 &*& first->next |-> ?next &*& malloc_block_node(first) &*& lseg(next, last);

lemma void nodes_to_lseg_lemma(struct node *first)
    requires list(first);
    ensures lseg(first, 0);
{
    open list(first);
    if (first != 0) {
        nodes_to_lseg_lemma(first->next);
    }
    close lseg(first, 0);
}

lemma void lseg_to_nodes_lemma(struct node *first)
    requires lseg(first, 0);
    ensures list(first);
{
    open lseg(first, 0);
    if (first != 0) {
        lseg_to_nodes_lemma(first->next);
    }
    close list(first);
}

lemma void lseg_add_lemma(struct node *first)
    requires lseg(first, ?last) &*& last != 0 &*& last->next |-> ?next &*& malloc_block_node(last) &*& lseg(next, 0);
    ensures lseg(first, next) &*& lseg(next, 0);
{
    open lseg(first, last);
    if (first == last) {
        close lseg(next, next);
    } else {
        lseg_add_lemma(first->next);
    }
    open lseg(next, 0);
    close lseg(next, 0);
    close lseg(first, next);
}

@*/

/*@

lemma void lseg_append_lemma(struct node *first)
    requires lseg(first, ?n) &*& lseg(n, 0);
    ensures lseg(first, 0);
{
    open lseg(first, n);
    if (first != n) {
        open lseg(n, 0);
        close lseg(n, 0);
        lseg_append_lemma(first->next);
        close lseg(first, 0);
    }
}

@*/

void push_all(struct node *this, struct node *other)
    //@ requires list(this) &*& list(other) &*& other != 0;
    //@ ensures list(other);
{
    //@ nodes_to_lseg_lemma(this);
    //@ nodes_to_lseg_lemma(other);
    struct node *n = other;
    //@ open lseg(n, 0);
    //@ close lseg(n, n);
    while (n->next != 0)
        /*@
        invariant
            lseg(other, n) &*&
            n != 0 &*& n->next |-> ?next &*& malloc_block_node(n) &*& lseg(next, 0);
        @*/
    {
        n = n->next;
        //@ lseg_add_lemma(other);
        //@ open lseg(next, 0);
    }
    //@ open lseg(0, 0);
    n->next = this;
    //@ lseg_add_lemma(other);
    //@ lseg_append_lemma(other);
    //@ lseg_to_nodes_lemma(other);
}

void push_all(struct node *this, struct node *other)
    //@ requires list(this) &*& list(other) &*& other != 0;
    //@ ensures list(other);
{
    //@ lemmas
    struct node *n = other;
    //@ open, close
    while (n->next != 0)
    //@ invariant
    {
        n = n->next;
        //@ lemma, open
    }
    //@ open
    n->next = this;
    //@ lemmas
}