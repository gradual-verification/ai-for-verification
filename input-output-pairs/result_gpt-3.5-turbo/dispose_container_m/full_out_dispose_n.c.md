```c CODE and SPEC
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

/****
 * Description:
The create_container function is a constructor for a container data structure.

@param none

The function creates a new container object by allocating memory for a struct container 
and sets its head pointer to NULL. The function takes no parameters and 
returns the newly created container.
*/
struct container *create_container()
    //@ requires true;
    //@ ensures \result != \null ==> \result->head == \null;
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0)
    {
        abort();
    }
    container->head = 0;
    return container;
}

/****
 * Description:
The container_add function adds an element to the container. 

@param container - pointer to the container
@param value - integer value to be added to the container

The function dynamically allocates memory for a new node, 
assigns the value to the node, and updates the head pointer 
of the container to point to the new node. The number of elements 
in the container is incremented by one.
*/
void container_add(struct container *container, int value)
    //@ requires container->head |-> ?head &*& malloc_block_container(container) &*& head->next |-> _ &*& head->value |-> _;
    //@ ensures malloc_block_node(\result) &*& \result->next == head &*& \result->value == value &*& container->head |-> \result;
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

/****
 * Description:
The container_remove function removes an element 
from the non-empty container.

@param container - pointer to the non-empty container

The function takes a pointer to the container as a parameter and 
retrieves the value of the top node. It then updates the 
head pointer of the container to the next node, frees the 
memory of the popped node, and returns the value.
*/
int container_remove(struct container *container)
    //@ requires container->head |-> ?head &*& malloc_block_container(container) &*& head->next |-> ?next &*& head->value |-> ?value;
    //@ ensures malloc_block_node(head) &*& malloc_block_container(container) &*& container->head |-> next &*& result == value;
{
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    free(head);
    return result;
}

/****
 * Description:
The nodes_dispose function recursively deallocates memory 
for all nodes in a linked list starting from a given node. 

@param n - pointer to the node to be disposed.

The function takes a pointer to a node as a parameter and traverses 
the linked list by recursively calling itself on the next 
node until reaching the end of the list. The function frees 
the memory of each node as it unwinds the recursion.
*/
void nodes_dispose(struct node *n)
    //@ requires n |-> ?node &*& malloc_block_node(node) &*& node->next |-> _ &*& node->value |-> _;
    //@ ensures true; 
{
    if (n != 0)
    {
        struct node *next = n->next;
        free(n);
        nodes_dispose(next);
    }
}

/****
 * Description:
The container_dispose function frees the memory of an entire 
container including all the nodes in its linked list. 

@param container - pointer to the container to be deleted.

It takes a pointer to the container as a parameter and calls 
nodes_dispose on the head of the container to deallocate 
memory for all nodes. Finally, it frees the memory of the 
container itself.
*/
void container_dispose(struct container *container)
    //@ requires malloc_block_container(container) &*& container->head |-> ?head &*& head->next |-> _ &*& head->value |-> _;
    //@ ensures true; 
{
    nodes_dispose(container->head);
    free(container);
}

/****
 * Description:
The main function creates a container, adds twice and removes twice, and finally disposes the container.
*/
int main()
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
    container_remove(s);
    container_remove(s);
    container_dispose(s);
    return 0;
}
```
