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

/***
 * Description:
The create_container function creates an empty container.
 
@return - A pointer to the newly created container.

This function allocates memory for a new container and initializes its head to NULL.
If memory allocation fails, the program aborts.
*/
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
The container_add function pushes a value onto the container.

@param container - A pointer to the container.
@param value - The integer value to push onto the container.

This function allocates a new node, assigns the given value to it,
and sets the new node as the head of the container.
If memory allocation fails, the program aborts.
*/
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
The container_remove function pops a value from the container.

@param container - A pointer to the container.
@return - The integer value popped from the container.

This function removes the head node from the container, retrieves its value,
and frees the memory allocated to the head node. The container must not be empty.
*/
int container_remove(struct container *container)
{
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    free(head);
    return result;
}

typedef bool int_predicate(int x);

/***
 * Description:
The nodes_filter function filters nodes based on a predicate.

@param n - A pointer to the node.
@param p - A predicate function to determine whether to keep a node.
@return - A pointer to the head of the filtered nodes list.

This function recursively filters the linked list of nodes, keeping only those
nodes for which the predicate function returns true. It frees the memory of the nodes
that do not satisfy the predicate.
*/
struct node *nodes_filter(struct node *n, int_predicate *p)
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            return result;
        }
    }
}

/***
 * Description:
The container_filter function filters the container based on a predicate.

@param container - A pointer to the container.
@param p - A predicate function to determine whether to keep a node.

This function filters the nodes in the container using the given predicate function.
It updates the container to contain only the nodes that satisfy the predicate.
*/
void container_filter(struct container *container, int_predicate *p)
{
    struct node *head = nodes_filter(container->head, p);
    container->head = head;
}

/***
 * Description:
The nodes_dispose function disposes of all nodes in a linked list.

@param n - A pointer to the head node.
 
This function recursively frees all nodes in the linked list.
*/
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
The container_dispose function disposes of a container.

@param container - A pointer to the container.

This function frees all nodes in the container and then frees the container itself.
*/
void container_dispose(struct container *container)
{
    nodes_dispose(container->head);
    free(container);
}

/***
 * Description:
The neq_20 function filters the container based on a predicate.

@param container - A pointer to the container.
@param p - A predicate function to determine whether to keep a node.
 
This function filters the nodes in the container using the given predicate function.
It updates the container to contain only the nodes that satisfy the predicate.
*/
bool neq_20(int x) //@ : int_predicate
{
    return x != 20;
}

/***
 * Description:
The main function creates a container, pushes some integers into it, 
filters out some integers from the container and finally disposes the container.
*/
int main()
{
    struct container *s = create_container();
    container_push(s, 10);
    container_push(s, 20);
    container_push(s, 30);
    container_filter(s, neq_20);
    container_dispose(s);
    return 0;
}
