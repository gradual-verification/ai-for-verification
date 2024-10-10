#include "stdlib.h"

/*@
predicate nodes(struct node *n;) =
    n == 0 ? true : 
    malloc_block_node(n) &*& n->value |-> ?v &*& n->next |-> ?next &*& nodes(next);

predicate container(struct container *c;) =
    malloc_block_container(c) &*& c->head |-> ?head &*& nodes(head);
@*/

struct node
{
    struct node *next;
    int value;
};

struct container
{
    struct node *head;
};

/***
 * Description:
The create_container function is a constructor for a container data structure.

@param none

The function creates a new container object by allocating memory for a struct container 
and sets its head pointer to NULL. The function takes no parameters and 
returns the newly created container.
*/
/*@
requires true;
ensures result != 0 &*& container(result);
@*/
struct container *create_container()
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0)
    {
        abort();
    }
    container->head = 0;
    return container;
}

/***
 * Description:
The container_add function adds an element to the container. 

@param container - pointer to the container
@param value - integer value to be added to the container

The function dynamically allocates memory for a new node, 
assigns the value to the node, and updates the head pointer 
of the container to point to the new node. The number of elements 
in the container is incremented by one.
*/
/*@
requires container(container);
ensures container(container);
@*/
void container_add(struct container *container, int value)
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

/***
 * Description:
The container_remove function removes an element 
from the non-empty container.

@param container - pointer to the non-empty container

The function takes a pointer to the container as a parameter and 
retrieves the value of the top node. It then updates the 
head pointer of the container to the next node, frees the 
memory of the popped node, and returns the value.
*/
/*@
requires container(container) &*& container->head != 0;
ensures container(container);
@*/
int container_remove(struct container *container)
{
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    free(head);
    return result;
}

/***
 * Description:
The nodes_dispose function recursively deallocates memory 
for all nodes in a linked list starting from a given node. 

@param n - pointer to the node to be disposed.

The function takes a pointer to a node as a parameter and traverses 
the linked list by recursively calling itself on the next 
node until reaching the end of the list. The function frees 
the memory of each node as it unwinds the recursion.
*/
/*@
requires nodes(n);
ensures true;
@*/
void nodes_dispose(struct node *n)
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

/***
 * Description:
The container_dispose function frees the memory of an entire 
container including all the nodes in its linked list. 

@param container - pointer to the container to be deleted.

It takes a pointer to the container as a parameter and calls 
nodes_dispose on the head of the container to deallocate 
memory for all nodes. Finally, it frees the memory of the 
container itself.
*/
/*@
requires container(container);
ensures true;
@*/
void container_dispose(struct container *container)
{
    nodes_dispose(container->head);
    free(container);
}

/***
 * Description:
The main function creates a container, adds twice and removes twice,
and finally dispose the container.
*/
/*@
requires true;
ensures true;
@*/
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
