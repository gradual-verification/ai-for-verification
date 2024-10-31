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
predicate nodes(struct node *node, list<int> values) =
    node == 0 ?
        values == nil
    :
        node->next |-> ?next &*& node->value |-> ?value &*&
        malloc_block_node(node) &*& nodes(next, ?next_values) &*&
        values == cons(value, next_values);

predicate container(struct container *container, list<int> values) =
    container->head |-> ?head &*& malloc_block_container(container) &*& nodes(head, values);
@*/

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
//@ requires container(container, ?values);
//@ ensures container(container, cons(value, values));
{
    //@ open container(container, values);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = container->head;
    n->value = value;
    container->head = n;
    //@ close nodes(n, cons(value, values));
    //@ close container(container, cons(value, values));
}

int container_remove(struct container *container)
//@ requires container(container, ?values) &*& values != nil;
//@ ensures container(container, tail(values)) &*& result == head(values);
{
    //@ open container(container, values);
    struct node *head = container->head;
    //@ open nodes(head, values);
    int result = head->value;
    container->head = head->next;
    free(head);
    //@ close container(container, tail(values));
    return result;
}

/*@
fixpoint list<int> nodes_filter_fp(fixpoint(int, bool) fp, list<int> values) {
    return filter(fp, values);
}
@*/

struct node *nodes_filter(struct node *n, fixpoint(int, bool) fp)
//@ requires nodes(n, ?values);
//@ ensures nodes(result, nodes_filter_fp(fp, values));
{
    if (n == 0)
    {
        //@ assert values == nil;
        //@ close nodes(0, nil);
        return 0;
    }
    else
    {
        //@ open nodes(n, values);
        bool keep = fp(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, fp);
            n->next = next;
            //@ close nodes(n, cons(n->value, nodes_filter_fp(fp, tail(values))));
            //@ assert nodes(n, cons(n->value, nodes_filter_fp(fp, tail(values))));
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, fp);
            //@ assert nodes(result, nodes_filter_fp(fp, tail(values)));
            return result;
        }
    }
}

/*@
lemma void filter_cons(fixpoint(int, bool) fp, int x, list<int> xs)
    requires true;
    ensures nodes_filter_fp(fp, cons(x, xs)) == (fp(x) ? cons(x, nodes_filter_fp(fp, xs)) : nodes_filter_fp(fp, xs));
{
    if (fp(x)) {
        // do nothing
    } else {
        // do nothing
    }
}
@*/

void container_filter(struct container *container, fixpoint(int, bool) fp)
//@ requires container(container, ?values);
//@ ensures container(container, nodes_filter_fp(fp, values));
{
    //@ open container(container, values);
    //@ close nodes(container->head, values); // Re-assert nodes predicate
    struct node *head = nodes_filter(container->head, fp);
    container->head = head;
    //@ close container(container, nodes_filter_fp(fp, values));
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
    else
    {
        //@ open nodes(n, _);
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

/*@
fixpoint bool neq_20(int x) { return x != 20; }
@*/

int main()
//@ requires true;
//@ ensures true;
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
    container_add(s, 30);
    container_filter(s, neq_20);
    container_dispose(s);
    return 0;
}
