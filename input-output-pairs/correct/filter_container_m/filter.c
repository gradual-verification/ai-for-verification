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
0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*&
malloc_block_node(node) &*& nodes(next, count - 1);

predicate container(struct container *container, int count) =
container->head |-> ?head &*& malloc_block_container(container) &*& 0 <= count &*& nodes(head, count);
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
    //@ close nodes(0, 0);
    //@ close container(container, 0);
    return container;
}

void container_add(struct container *container, int value)
//@ requires container(container, ?count);
//@ ensures container(container, count + 1);
{
    //@ open container(container, count);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0)
    {
        abort();
    }
    n->next = container->head;
    n->value = value;
    container->head = n;
    //@ close nodes(n, count + 1);
    //@ close container(container, count + 1);
}

int container_remove(struct container *container)
//@ requires container(container, ?count) &*& 0 < count;
//@ ensures container(container, count - 1);
{
    //@ open container(container, count);
    struct node *head = container->head;
    //@ open nodes(head, count);
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
    if (n == 0)
    {
        return 0;
    }
    else
    {
        //@ open nodes(n, _);
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            //@ open nodes(next, ?count);
            //@ close nodes(next, count);
            n->next = next;
            //@ close nodes(n, count + 1);
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

void container_filter(struct container *container, int_predicate *p)
//@ requires container(container, _) &*& is_int_predicate(p) == true;
//@ ensures container(container, _);
{
    //@ open container(container, _);
    struct node *head = nodes_filter(container->head, p);
    //@ assert nodes(head, ?count);
    container->head = head;
    //@ open nodes(head, count);
    //@ close nodes(head, count);
    //@ close container(container, count);
}

void nodes_dispose(struct node *n)
//@ requires nodes(n, _);
//@ ensures true;
{
    //@ open nodes(n, _);
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
