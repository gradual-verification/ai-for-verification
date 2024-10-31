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
predicate nodes(struct node *node, int count) =
node == 0 ?
    count == 0
:
    0 < count &*&
    node->next |-> ?next &*&
    node->value |-> _ &*&
    nodes(next, count - 1);

predicate container(struct container *container, int count) =
    container->head |-> ?head &*& nodes(head, count);
@*/

struct container *create_container()
//@ requires true;
//@ ensures container(result, 0);
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0)
    {
        abort();
    }
    container->head = 0;
    //@ close container(container, 0);
    return container;
}

void container_add(struct container *container, int value)
//@ requires container(container, ?count);
//@ ensures container(container, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->value = value;
    n->next = container->head;
    container->head = n;
    //@ close nodes(n, count + 1);
    //@ close container(container, count + 1);
}

void container_remove(struct container *container)
//@ requires container(container, ?count) &*& 0 < count;
//@ ensures container(container, count - 1);
{
    struct node *head = container->head;
    container->head = head->next;
    //@ open nodes(head, count);
    //@ open container(container, count);
    free(head);
    //@ close container(container, count - 1);
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

int main()
//@ requires true;
//@ ensures true;
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
    container_remove(s);
    container_remove(s);
    container_dispose(s);
    return 0;
}
