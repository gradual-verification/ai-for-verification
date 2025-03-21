#include "stdlib.h"

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@

predicate nodes(struct node *node, int count) =
    node == 0 ? count == 0 : 0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

@*/

/*@

predicate lseg(struct node *first, struct node *last, int count) =
    first == last ?
        count == 0
    :
        0 < count &*& first != 0 &*&
        first->value |-> ?value &*& first->next |-> ?next &*& malloc_block_node(first) &*&
        lseg(next, last, count - 1);

lemma void nodes_to_lseg_lemma(struct node *first)
    requires nodes(first, ?count);
    ensures lseg(first, 0, count);
{
    open nodes(first, count);
    if (first != 0) {
        nodes_to_lseg_lemma(first->next);
    }
    close lseg(first, 0, count);
}

lemma void lseg_to_nodes_lemma(struct node *first)
    requires lseg(first, 0, ?count);
    ensures nodes(first, count);
{
    open lseg(first, 0, count);
    if (first != 0) {
        lseg_to_nodes_lemma(first->next);
    }
    close nodes(first, count);
}

lemma void lseg_add_lemma(struct node *first)
    requires lseg(first, ?last, ?count) &*& last != 0 &*& last->value |-> ?lastValue &*& last->next |-> ?next &*& malloc_block_node(last) &*& lseg(next, 0, ?count0);
    ensures lseg(first, next, count + 1) &*& lseg(next, 0, count0);
{
    open lseg(first, last, count);
    if (first == last) {
        close lseg(next, next, 0);
    } else {
        lseg_add_lemma(first->next);
    }
    open lseg(next, 0, count0);
    close lseg(next, 0, count0);
    close lseg(first, next, count + 1);
}

@*/

int stack_get_count(struct stack *stack)
    //@ requires stack(stack, ?count) &*& count <= INT_MAX;
    //@ ensures stack(stack, count) &*& result == count;
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ nodes_to_lseg_lemma(head);
    struct node *n = head;
    int i = 0;
    //@ close lseg(head, head, 0);
    while (n != 0)
        //@ invariant lseg(head, n, i) &*& lseg(n, 0, count - i) &*& i <= count &*& count <= INT_MAX;
    {
        //@ open lseg(n, 0, count - i);
        n = n->next;
        i++;
        //@ lseg_add_lemma(head);
    }
    //@ open lseg(0, 0, _);
    //@ lseg_to_nodes_lemma(head);
    //@ close stack(stack, count);
    return i;
}

/*@

lemma void lseg_append_lemma(struct node *first)
    requires lseg(first, ?n, ?count) &*& lseg(n, 0, ?count0);
    ensures lseg(first, 0, count + count0);
{
    open lseg(first, n, count);
    if (first != n) {
        open lseg(n, 0, count0);
        close lseg(n, 0, count0);
        lseg_append_lemma(first->next);
        close lseg(first, 0, count + count0);
    }
}

@*/

void stack_push_all(struct stack *stack, struct stack *other)
    //@ requires stack(stack, ?count) &*& stack(other, ?count0);
    //@ ensures stack(stack, count0 + count);
{
    //@ open stack(stack, count);
    //@ nodes_to_lseg_lemma(stack->head);
    //@ open stack(other, count0);
    //@ nodes_to_lseg_lemma(other->head);
    struct node *head0 = other->head;
    free(other);
    struct node *n = head0;
    //@ open lseg(head0, 0, count0);
    if (n != 0) {
        //@ close lseg(head0, head0, 0);
        while (n->next != 0)
            /*@
            invariant
                lseg(head0, n, ?count1) &*&
                n != 0 &*& n->value |-> ?nValue &*& n->next |-> ?next &*& malloc_block_node(n) &*& lseg(next, 0, count0 - count1 - 1);
            @*/
        {
            n = n->next;
            //@ lseg_add_lemma(head0);
            //@ open lseg(next, 0, count0 - count1 - 1);
        }
        //@ open lseg(0, 0, _);
        n->next = stack->head;
        //@ lseg_add_lemma(head0);
        //@ lseg_append_lemma(head0);
        stack->head = head0;
    }
    //@ lseg_to_nodes_lemma(stack->head);
    //@ close stack(stack, count0 + count);
}