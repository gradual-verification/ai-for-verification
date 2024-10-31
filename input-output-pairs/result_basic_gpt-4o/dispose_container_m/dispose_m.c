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
    0 < count
    &*& node->next |-> ?next &*& node->value |-> ?value
    &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate container(struct container *container, int count) =
    container->head |-> ?head &*& malloc_block_container(container) &*& 0 <= count &*& nodes(head, count);
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
    //@ close nodes(0, 0);
    //@ close container(container, 0);
    container->head = 0;
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
    n->next = container->head;
    n->value = value;
    //@ close nodes(n, count + 1);
    container->head = n;
    //@ open container(container, count);
    //@ close container(container, count + 1);
}

void container_remove(struct container *container)
//@ requires container(container, ?count) &*& 0 < count;
//@ ensures container(container, count - 1);
{
    //@ open container(container, count);
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    //@ open nodes(head, count);
    //@ close container(container, count - 1);
    free(head);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, _);
//@ ensures true;
{
    if (n != 0)
    {
        struct node *next = n->next;
        //@ open nodes(n, _);
        nodes_dispose(next);
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
