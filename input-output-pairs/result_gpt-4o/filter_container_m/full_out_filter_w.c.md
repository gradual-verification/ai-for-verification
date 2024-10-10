```c
#include "stdlib.h"

// Definition of a singly linked list node
struct node {
    struct node *next;
    int value;
};

// Definition of a container holding a linked list of nodes
struct container {
    struct node *head;
};

/*@
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0 :
        0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*&
        nodes(next, count - 1);

predicate container(struct container *container, int count) =
    container->head |-> ?head &*& 0 <= count &*& nodes(head, count);

predicate_ctor is_int_predicate(int_predicate *p)() =
    true;
@*/

// Function to create and initialize a new container
struct container *create_container()
    //@ requires true;
    //@ ensures container(result, 0);
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0) {
        abort();
    }
    container->head = 0;
    return container;
}

// Function to push a value onto the container's linked list
void container_push(struct container *container, int value)
    //@ requires container(container, ?count);
    //@ ensures container(container, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->next = container->head;
    n->value = value;
    container->head = n;
}

// Function to pop a value from the container's linked list
int container_pop(struct container *container)
    //@ requires container(container, ?count) &*& 0 < count;
    //@ ensures container(container, count - 1);
{
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    free(head);
    return result;
}

// Definition of a function type for predicates on integers
typedef bool int_predicate(int x);
    //@ requires true;
    //@ ensures true;

// Function to filter nodes in a linked list using a predicate
struct node *nodes_filter(struct node *n, int_predicate *p)
    //@ requires nodes(n, ?count) &*& is_int_predicate(p)();
    //@ ensures nodes(result, _);
{
    if (n == 0) {
        return 0;
    } else {
        bool keep = p(n->value);
        if (keep) {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        } else {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            return result;
        }
    }
}

// Function to filter nodes in the container's linked list using a predicate
void container_filter(struct container *container, int_predicate *p)
    //@ requires container(container, ?count) &*& is_int_predicate(p)();
    //@ ensures container(container, _);
{
    struct node *head = nodes_filter(container->head, p);
    container->head = head;
}

// Function to dispose of a linked list of nodes
void nodes_dispose(struct node *n)
    //@ requires nodes(n, _);
    //@ ensures true;
{
    if (n != 0) {
        nodes_dispose(n->next);
        free(n);
    }
}

// Function to dispose of a container and its nodes
void container_dispose(struct container *container)
    //@ requires container(container, _);
    //@ ensures true;
{
    nodes_dispose(container->head);
    free(container);
}

// Implementation of an int_predicate that returns true if a value is not 20
bool neq_20(int x) //@ : int_predicate
    //@ requires true;
    //@ ensures true;
{
    return x != 20;
}

// Main function to test container operations
int main()
    //@ requires true;
    //@ ensures true;
{
    struct container *s = create_container();
    container_push(s, 10);
    container_push(s, 20);
    container_push(s, 30);
    container_filter(s, neq_20);
    container_dispose(s);
    return 0;
}
```

This code integrates verification annotations using VeriFast, ensuring that the linked list operations respect the contracts defined by the `nodes` and `container` predicates. The predicates state that a `container` holds a linked list with a specified number of nodes, and `nodes` describes a linked list with a specific count of nodes. Each function's preconditions and postconditions assert the preservation of these properties throughout the program's execution.
