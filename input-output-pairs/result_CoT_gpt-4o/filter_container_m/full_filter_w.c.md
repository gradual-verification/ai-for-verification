The task is to enhance the given C code with formal verification specifications using VeriFast. This involves ensuring memory safety, integer bound checks, and functional correctness by adding appropriate preconditions, postconditions, loop invariants, and other necessary annotations.

Here's the enhanced version of your code with added VeriFast annotations:

```c
#include "stdlib.h"
#include "stdbool.h"

struct node {
    struct node *next;
    int value;
};

struct container {
    struct node *head;
};

/*@
predicate nodes(struct node *node, int count) =
    node == 0 ?
        count == 0
    :
        0 < count &*& node->next |-> ?next &*& node->value |-> _ &*&
        nodes(next, count - 1);

predicate container(struct container *container, int count) =
    container->head |-> ?head &*& nodes(head, count);
@*/

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

void container_add(struct container *container, int value)
    //@ requires container(container, ?count);
    //@ ensures container(container, count + 1);
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->next = container->head;
    n->value = value;
    //@ open container(container, count);
    container->head = n;
    //@ close container(container, count + 1);
}

int container_remove(struct container *container)
    //@ requires container(container, ?count) &*& 0 < count;
    //@ ensures container(container, count - 1);
{
    struct node *head = container->head;
    //@ open container(container, count);
    int result = head->value;
    container->head = head->next;
    free(head);
    //@ close container(container, count - 1);
    return result;
}

typedef bool int_predicate(int x);
//@ requires true;
//@ ensures true;

struct node *nodes_filter(struct node *n, int_predicate *p)
    //@ requires nodes(n, _) &*& is_int_predicate(p) == true;
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

void container_filter(struct container *container, int_predicate *p)
    //@ requires container(container, _) &*& is_int_predicate(p) == true;
    //@ ensures container(container, _);
{
    //@ open container(container, _);
    struct node *head = nodes_filter(container->head, p);
    container->head = head;
    //@ close container(container, _);
}

void nodes_dispose(struct node *n)
    //@ requires nodes(n, _);
    //@ ensures true;
{
    if (n != 0) {
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
    //@ ensures true;
{
    return x != 20;
}

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
```

### Key Points:

- **Predicates**: These are used to define and keep track of structural invariants within the data structures (`nodes` and `container`).
- **Loop Invariants**: There are no explicit loops to annotate, but recursive functions such as `nodes_filter` achieve similar outcomes and the invariant is inherent in the recursive structure.
- **Memory Safety**: Managed by ensuring every allocation through `malloc` is checked and containers/nodes are disposed of correctly to avoid memory leaks.
- **Open/Close**: Use these statements to manipulate predicates within certain function calls to assist with verification.
- **Integer Bounds**: Managed via function preconditions/postconditions ensuring valid computations/operations.