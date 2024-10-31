#include "stdlib.h"

/*@
fixpoint list<int> filter(fixpoint(int, bool) pred, list<int> xs) {
    return xs == nil ? nil :
           pred(head(xs)) ? cons(head(xs), filter(pred, tail(xs))) :
           filter(pred, tail(xs));
}

predicate nodes(struct node *node; list<int> values) =
    node == 0 ? values == nil :
    node->next |-> ?next &*& node->value |-> ?value &*&
    nodes(next, ?next_values) &*& values == cons(value, next_values);

predicate container(struct container *container; list<int> values) =
    container->head |-> ?head &*& nodes(head, values);

predicate is_int_predicate(int_predicate *p; fixpoint(int, bool) pred);
@*/

struct node
{
    struct node *next;
    int value;
};

struct container
{
    struct node *head;
};

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
    return container;
}

void container_push(struct container *container, int value)
//@ requires container(container, ?values);
//@ ensures container(container, cons(value, values));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = container->head;
    n->value = value;
    container->head = n;
}

/*@
typedef bool int_predicate(int x);
    requires is_int_predicate(this, ?pred);
    ensures is_int_predicate(this, pred) &*& result == pred(x);
@*/

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?values) &*& is_int_predicate(p, ?pred);
//@ ensures nodes(result, filter(pred, values)) &*& is_int_predicate(p, pred);
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        //@ open nodes(n, values);
        bool keep = p(n->value);
        //@ open is_int_predicate(p, pred);
        //@ close is_int_predicate(p, pred);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            //@ close nodes(n, _);
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            //@ close nodes(result, _);
            return result;
        }
    }
}

void container_filter(struct container *container, int_predicate *p)
//@ requires container(container, ?values) &*& is_int_predicate(p, ?pred);
//@ ensures container(container, filter(pred, values)) &*& is_int_predicate(p, pred);
{
    struct node *head = nodes_filter(container->head, p);
    container->head = head;
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
    nodes_dispose(container->head);
    free(container);
}

/*@
fixpoint bool neq_20_fp(int x) { return x != 20; }

lemma void neq_20_is_int_predicate()
//@ requires true;
//@ ensures is_int_predicate(neq_20, neq_20_fp);
{
    close is_int_predicate(neq_20, neq_20_fp);
}
@*/

bool neq_20(int x) //@ : int_predicate
//@ requires is_int_predicate(neq_20, ?pred);
//@ ensures is_int_predicate(neq_20, pred) &*& result == pred(x);
{
    //@ open is_int_predicate(neq_20, pred);
    //@ assert pred == neq_20_fp;
    bool res = x != 20;
    //@ close is_int_predicate(neq_20, pred);
    return res;
}

int main()
//@ requires true;
//@ ensures true;
{
    struct container *s = create_container();
    container_push(s, 10);
    container_push(s, 20);
    container_push(s, 30);
    //@ neq_20_is_int_predicate();
    container_filter(s, neq_20);
    container_dispose(s);
    return 0;
}
