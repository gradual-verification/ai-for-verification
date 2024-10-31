```c
#include "stdlib.h"
//@ #include "listex.gh"

struct node
{
    struct node *next;
    int value;
};

struct container
{
    struct node *head;
};

//@ predicate nodes(struct node *n; list<int> vs) =
//@     n == 0 ? vs == nil :
//@     n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vsNext) &*& vs == cons(v, vsNext);

//@ predicate container(struct container *c; list<int> vs) =
//@     c->head |-> ?h &*& nodes(h, vs) &*& malloc_block_container(c);

/***
 * Description:
The create_container function creates an empty container.

@return - A pointer to the newly created container.

This function allocates memory for a new container and initializes its head to NULL.
If memory allocation fails, the program aborts.
*/
//@ requires true;
//@ ensures container(result, nil);
struct container *create_container()
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0)
    {
        abort();
    }
    container->head = 0;
    //@ close nodes(0, nil);
    //@ close container(container, nil);
    return container;
}

/***
 * Description:
The container_add function adds a value onto the container.

@param container - A pointer to the container.
@param value - The integer value to push onto the container.

This function allocates a new node, assigns the given value to it,
and sets the new node as the head of the container.
If memory allocation fails, the program aborts.
*/
//@ requires container(container, ?vs);
//@ ensures container(container, cons(value, vs));
void container_add(struct container *container, int value)
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = container->head;
    n->value = value;
    //@ close malloc_block_node(n);
    //@ open container(container, vs);
    //@ close nodes(n, cons(value, vs));
    container->head = n;
    //@ close container(container, cons(value, vs));
}

/***
 * Description:
The container_remove function removes a value from the container.

@param container - A pointer to the container.
@return - The integer value popped from the container.

This function removes the head node from the container, retrieves its value,
and frees the memory allocated to the head node. The container must not be empty.
*/
//@ requires container(container, ?vs) &*& vs != nil;
//@ ensures container(container, tail(vs)) &*& result == head(vs);
int container_remove(struct container *container)
{
    //@ open container(container, vs);
    struct node *head = container->head;
    //@ open nodes(head, vs);
    int result = head->value;
    container->head = head->next;
    //@ close container(container, tail(vs));
    //@ open nodes(head, cons(result, tail(vs)));
    free(head);
    return result;
}

//@ predicate_family is_int_predicate(void *p)(fixpoint(int, bool) fp);

typedef bool int_predicate_t(int x);
//@ requires is_int_predicate(this)(?fp);
//@ ensures is_int_predicate(this)(fp) &*& result == fp(x);

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
//@ requires nodes(n, ?vs) &*& is_int_predicate(p)(?fp);
//@ ensures nodes(result, filter(fp, vs)) &*& is_int_predicate(p)(fp);
struct node *nodes_filter(struct node *n, int_predicate_t *p)
{
    if (n == 0)
    {
        //@ open nodes(0, _);
        return 0;
    }
    else
    {
        //@ open nodes(n, vs);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            //@ vs == cons(n->value, ?vsNext);
            //@ filter(fp, vs) == cons(n->value, filter(fp, vsNext));
            //@ close nodes(n, cons(n->value, filter(fp, vsNext)));
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            //@ vs == cons(n->value, ?vsNext);
            struct node *result = nodes_filter(next, p);
            //@ close nodes(result, filter(fp, vsNext));
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
//@ requires container(container, ?vs) &*& is_int_predicate(p)(?fp);
//@ ensures container(container, filter(fp, vs)) &*& is_int_predicate(p)(fp);
void container_filter(struct container *container, int_predicate_t *p)
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
//@ requires nodes(n, _);
//@ ensures emp;
void nodes_dispose(struct node *n)
{
    if (n != 0)
    {
        //@ open nodes(n, _);
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
//@ requires container(container, _);
//@ ensures emp;
void container_dispose(struct container *container)
{
    //@ open container(container, _);
    nodes_dispose(container->head);
    free(container);
}

//@ fixpoint bool neq_20_fp(int x) { return x != 20; }

lemma void neq_20_is_int_predicate()
//@ requires true;
//@ ensures is_int_predicate(neq_20)(neq_20_fp);
{
    //@ close is_int_predicate(neq_20)(neq_20_fp);
}

/***
 * Description:
The neq_20 function filters the container based on a predicate.

@param x - The integer to compare.

This function returns true if x is not equal to 20.
*/
//@ requires is_int_predicate(neq_20)(?fp);
//@ ensures is_int_predicate(neq_20)(fp) &*& result == fp(x);
bool neq_20(int x) //@ : int_predicate_t
{
    //@ open is_int_predicate(neq_20)(fp);
    //@ close is_int_predicate(neq_20)(fp);
    return x != 20;
}

/***
 * Description:
The main function creates a container, pushes some integers into it,
filters out some integers from the container and finally disposes the container.
*/
//@ requires true;
//@ ensures true;
int main()
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
    container_add(s, 30);
    //@ neq_20_is_int_predicate();
    container_filter(s, neq_20);
    container_dispose(s);
    return 0;
}
```
