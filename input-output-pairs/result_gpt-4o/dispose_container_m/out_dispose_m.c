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
    container->head |-> ?head &*& malloc_block_container(container) 
    &*& 0 <= count &*& nodes(head, count);
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
    container->head = n;
}

void container_remove(struct container *container)
//@ requires container(container, ?count) &*& 0 < count;
//@ ensures container(container, count - 1);
{
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    free(head);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, _);
//@ ensures true;
{
    if (n != 0)
    {
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

int main()
//@ requires true;
//@ ensures true;
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
  
    // Verify by checking the preconditions before removing
    // This requires adding verification for ensuring the count is > 0
    //@ assert container(s, 2); 

    container_remove(s);
    //@ assert container(s, 1); 

    container_remove(s);
    //@ assert container(s, 0); 

    container_dispose(s);
    return 0;
}
