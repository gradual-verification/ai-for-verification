#include "stdlib.h"

struct node
{
    struct node *next;
    int value;
};

//@ predicate nodes(struct node *n; list<int> vs) = n == 0 ? vs == nil : malloc_block_node(n) &*& n->value |-> ?v &*& n->next |-> ?next &*& nodes(next, ?tail) &*& vs == cons(v, tail);

struct container
{
    struct node *head;
};

//@ predicate container(struct container *c; list<int> vs) = c->head |-> ?head &*& nodes(head, vs);

//@ ensures result == 0 ? true : container(result, nil);
struct container *create_container()
    //@ requires true;
    //@ ensures result == 0 ? true : container(result, nil);
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0)
    {
        abort();
    }
    container->head = 0;
    return container;
}

//@ requires container(container, ?vs);
//@ ensures container(container, cons(value, vs));
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
    container->head = n;
}

//@ requires container(container, cons(?value, ?vs));
//@ ensures container(container, vs);
void container_remove(struct container *container)
    //@ requires container(container, cons(?value, ?vs));
    //@ ensures container(container, vs);
{
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    free(head);
}

//@ requires nodes(n, ?vs);
//@ ensures true;
void nodes_dispose(struct node *n)
    //@ requires nodes(n, ?vs);
    //@ ensures true;
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

//@ requires container(container, ?vs);
//@ ensures true;
void container_dispose(struct container *container)
    //@ requires container(container, ?vs);
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
    if (s != 0) {
        container_add(s, 10);
        container_add(s, 20);
        container_remove(s);
        container_remove(s);
        container_dispose(s);
    }
    return 0;
}
