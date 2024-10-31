#include "stdlib.h"

/*@
predicate nodes(struct node *n; list<int> vs) =
    n == 0 ?
        vs == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& nodes(next, ?vs_rest) &*& vs == cons(v, vs_rest);

predicate container(struct container *c; list<int> vs) =
    c->head |-> ?h &*& nodes(h, vs);
@*/

struct node {
    struct node *next;
    int value;
};

struct container {
    struct node *head;
};

struct container *create_container()
    //@ requires emp;
    //@ ensures result != 0 &*& container(result, nil);
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0) {
        abort();
    }
    //@ close malloc_block_container(container);
    //@ container->head |-> _;
    container->head = 0;
    //@ container->head |-> 0;
    //@ close nodes(0, nil);
    //@ close container(container, nil);
    return container;
}

void container_add(struct container *container, int value)
    //@ requires container(container, ?vs);
    //@ ensures container(container, cons(value, vs));
{
    //@ open container(container, vs);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    //@ close malloc_block_node(n);
    //@ n->next |-> _;
    //@ n->value |-> _;
    n->next = container->head;
    //@ n->next |-> container->head;
    n->value = value;
    //@ n->value |-> value;
    container->head = n;
    //@ container->head |-> n;
    //@ close nodes(n, cons(value, vs));
    //@ close container(container, cons(value, vs));
}

void container_remove(struct container *container)
    //@ requires container(container, ?vs) &*& vs != nil;
    //@ ensures container(container, tail(vs));
{
    //@ open container(container, vs);
    struct node *head = container->head;
    //@ open nodes(head, vs);
    int result = head->value;
    container->head = head->next;
    //@ container->head |-> head->next;
    //@ head->value |-> result;
    //@ head->next |-> head->next;
    //@ malloc_block_node(head);
    free(head);
    //@ dispose_block_node(head);
    //@ close container(container, tail(vs));
}

void nodes_dispose(struct node *n)
    //@ requires nodes(n, _);
    //@ ensures emp;
{
    if (n != 0) {
        //@ open nodes(n, _);
        nodes_dispose(n->next);
        //@ n->value |-> _;
        //@ n->next |-> _;
        //@ malloc_block_node(n);
        free(n);
        //@ dispose_block_node(n);
    }
}

void container_dispose(struct container *container)
    //@ requires container(container, _);
    //@ ensures emp;
{
    //@ open container(container, _);
    nodes_dispose(container->head);
    //@ container->head |-> _;
    //@ malloc_block_container(container);
    free(container);
    //@ dispose_block_container(container);
}

int main()
    //@ requires emp;
    //@ ensures emp;
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
    container_remove(s);
    container_remove(s);
    container_dispose(s);
    return 0;
}
