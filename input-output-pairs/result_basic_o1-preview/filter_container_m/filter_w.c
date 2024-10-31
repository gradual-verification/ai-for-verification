#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

struct container
{
    struct node *head;
};

/*@
predicate nodes(struct node *node; list<int> vs) =
    node == 0 ?
        vs == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*&
        nodes(next, ?vs_next) &*&
        vs == cons(value, vs_next);

predicate container(struct container *container; list<int> vs) =
    container->head |-> ?head &*& nodes(head, vs);

fixpoint list<int> filter_fp(fixpoint(int, bool) p, list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(x, xs0): return p(x) ? cons(x, filter_fp(p, xs0)) : filter_fp(p, xs0);
    }
}

fixpoint bool neq_20_fp(int x) { return x != 20; }

predicate is_int_predicate(int_predicate *p; fixpoint(int, bool) pred) = true;

@*/

typedef bool int_predicate(int x);

struct container *create_container()
//@ requires true;
//@ ensures container(result, nil);
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0)
    {
        abort();
    }
    container->head = 0;
    //@ close nodes(0, nil);
    //@ close container(container, nil);
    return container;
}

void container_add(struct container *container, int value)
//@ requires container(container, ?vs);
//@ ensures container(container, cons(value, vs));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = container->head;
    n->value = value;
    //@ close nodes(n, cons(value, vs));
    container->head = n;
    //@ close container(container, cons(value, vs));
}

int container_remove(struct container *container)
//@ requires container(container, ?vs) &*& vs != nil;
//@ ensures container(container, ?vs_tail) &*& vs == cons(result, vs_tail);
{
    //@ open container(container, vs);
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    //@ open nodes(head, vs);
    //@ vs == cons(result, ?vs_tail);
    //@ close container(container, vs_tail);
    free(head);
    return result;
}

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?vs) &*& is_int_predicate(p, ?pred);
//@ ensures nodes(result, filter_fp(pred, vs));
{
    if (n == 0)
    {
        //@ close nodes(0, nil);
        return 0;
    }
    else
    {
        //@ open nodes(n, vs);
        bool keep = p(n->value);
        //@ assert keep == pred(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            //@ close nodes(n, cons(n->value, filter_fp(pred, ?vs_next)));
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            return result;
        }
    }
}

void container_filter(struct container *container, int_predicate *p)
//@ requires container(container, ?vs) &*& is_int_predicate(p, ?pred);
//@ ensures container(container, filter_fp(pred, vs));
{
    //@ open container(container, vs);
    struct node *head = nodes_filter(container->head, p);
    container->head = head;
    //@ close container(container, filter_fp(pred, vs));
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, _);
//@ ensures true;
{
    if (n != 0)
    {
        //@ open nodes(n, _);
        nodes_dispose(n->next);
        free(n);
    }
}

void container_dispose(struct container *container)
//@ requires container(container, _);
//@ ensures true;
{
    //@ open container(container, _);
    nodes_dispose(container->head);
    free(container);
}

bool neq_20(int x) //@ : int_predicate
//@ requires true;
//@ ensures result == neq_20_fp(x);
{
    return x != 20;
}

/*@
lemma void neq_20_spec()
    requires true;
    ensures is_int_predicate(neq_20, neq_20_fp);
{
}
@*/

int main()
//@ requires true;
//@ ensures true;
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
    container_add(s, 30);
    //@ neq_20_spec();
    container_filter(s, neq_20);
    container_dispose(s);
    return 0;
}
