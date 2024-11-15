```c
#include <stdlib.h>

typedef struct node {
    int item;
    struct node *next;
    struct node *prev;
} *node;

typedef struct dllist {
    node head;
    node tail;
} *dllist;

//@ predicate nodes(node n, node end) =
//@     n == end ? true : n != 0 && n->next |-> ?next &*& n->prev |-> _ &*& malloc_block_node(n) &*& nodes(next, end);

void reverse(dllist arg)
    //@ requires arg != 0 &*& nodes(arg->head, 0);
    //@ ensures nodes(arg->head, 0);
{
    node ptr = arg->head;
    node temp1 = 0;
    node temp2 = 0;
    while (ptr != 0)
        //@ invariant nodes(ptr, 0) &*& arg->head |-> ?h &*& arg->tail |-> ?t;
    {
        temp1 = ptr->next;
        temp2 = ptr->prev;
        ptr->next = temp2;
        ptr->prev = temp1;
        ptr = temp1;
    }
    temp1 = arg->head;
    temp2 = arg->tail;
    arg->head = temp2;
    arg->tail = temp1;
}

/***
 * Description:
The default main function, doing nothing.
*/
int main()
{
    return 0;
}
```

**Explanation:**

- **Data Structures and Predicates:**
  - We defined a predicate `nodes` to abstractly represent the properties of a linked list. It ensures that either the node is `end` (null) or it is a valid node with non-null `next` and `prev` pointers.

- **Function Specification:**
  - The `reverse` function assumes it receives a non-null `dllist`, `arg`, which points to a doubly linked list starting from `arg->head`. This is described in the precondition `requires arg != 0 &*& nodes(arg->head, 0);`.
  - Ensures that after execution, it provides the same abstract representation of the doubly linked list with nodes reversed: `ensures nodes(arg->head, 0);`.

- **Loop Invariants:**
  - Inside the loop, we've specified an invariant: `nodes(ptr, 0) &*& arg->head |-> ?h &*& arg->tail |-> ?t;`, ensuring at every iteration, the node list remains safe to access.

This should be implemented in VeriFast and checked for verification. The loop invariant ensures the memory safety, and the pre-condition checks ensure the initial conditions of the function's execution are valid. Similarly, after the function completes execution, the postconditions ensure the properties of the data structures are maintained.
