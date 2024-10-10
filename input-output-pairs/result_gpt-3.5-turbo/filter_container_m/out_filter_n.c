
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

/*@null@*/
struct node * nodes_filter(struct node *n, int_predicate *p);

/*@null@*/
void container_filter(struct container *container, int_predicate *p);

/*@null@*/
void nodes_dispose(struct node *n);

/*@null@*/
void container_dispose(struct container *container);

typedef bool int_predicate(int x);

/*@axiomatic Predicate
predicate neq_20(int x) reads x
{
  return x != 20;
}

lemma void lemma_propagate_nodes_filter_pred(struct node *n, int_predicate *p)
requires n != 0 &*& nodes_filter(n, p) == 0;
ensures forall(filter_nodes, p);
{
  if (n->value == 20)
  {
    lemma_propagate_nodes_filter_pred(n->next, p);
  }
}

lemma void lemma_propagate_container_filter_pred(struct container *container, int_predicate *p)
requires container->head != 0 &*& container_filter(container, p) == 0;
ensures forall(filter_nodes, p);
{
  lemma_propagate_nodes_filter_pred(container->head, p);
}

lemma void lemma_propagate_nodes_dispose(struct node *n)
requires n == 0 &*& nodes_dispose(n) == 0;
ensures true;
{
}

lemma void lemma_propagate_container_dispose(struct container *container)
requires container->head == 0 &*& container_dispose(container) == 0;
ensures true;
{
}

lemma void neq_20_prop(int x)
requires neq_20(x);
ensures x != 20;
{
}

struct container *create_container()
//@ requires true;
//@ ensures result != 0 &*& result->head == 0;
{
    struct container *container = malloc(sizeof(struct container));
    if (container == 0)
    {
        abort();
    }
    container->head = 0;
    return container;
}

void container_add(struct container *container, int value)
//@ requires container->head |-> ?head &*& malloc_block_container(container) &*& is_container_cons(container, head) == true;
//@ ensures container->head |-> ?newHead &*& malloc_block_container(container) &*& is_container_cons(container, newHead);
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

int container_remove(struct container *container)
//@ requires container->head |-> ?head &*& malloc_block_container(container) &*& is_container_cons(container, head) == true;
//@ ensures container->head |-> ?newHead &*& malloc_block_container(container) &*& is_container_cons(container, newHead) == true;
{
    struct node *head = container->head;
    int result = head->value;
    container->head = head->next;
    free(head);
    return result;
}

void container_filter(struct container *container, int_predicate *p)
//@ requires container->head |-> ?head &*& malloc_block_container(container) &*& is_container_cons(container, head) == true;
//@ ensures container->head |-> ?newHead &*& malloc_block_container(container) &*& is_container_cons(container, newHead);
{
    container->head = nodes_filter(container->head, p);
}

struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires is_node(n,?value,_);
//@ ensures is_node(_,?new_value,?) &*& is_node(_,_,_);
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

void nodes_dispose(struct node *n)
//@ requires true;
//@ ensures true;
{
    if (n != 0)
    {
        nodes_dispose(n->next);
        free(n);
    }
}

void container_dispose(struct container *container)
//@ requires container->head |-> ?head &*& malloc_block_container(container) &*& is_container_cons(container, head) == true;
//@ ensures true;
{
    nodes_dispose(container->head);
    free(container);
}

int main()
{
    struct container *s = create_container();
    container_add(s, 10);
    container_add(s, 20);
    container_add(s, 30);
    container_filter(s, neq_20);
    container_dispose(s);
    return 0;
}
