#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

struct iter {
    struct node *current;
};

/*@
predicate nodes(struct node *n; list<int> vs) =
    n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *l; list<int> vs) =
    l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*& nodes(first, vs) &*& (vs == nil ? first == last : last->next |-> 0 &*& last->value |-> _ &*& malloc_block_node(last));

predicate iter(struct iter *i, struct llist *l, list<int> vs) =
    i->current |-> ?current &*& malloc_block_iter(i) &*& llist(l, vs) &*& nodes(current, ?vs0) &*& mem(current, vs0) == true;
@*/

/*@
lemma void nodes_to_llist_lemma(struct node *first)
    requires nodes(first, ?vs);
    ensures nodes(first, vs) &*& (vs == nil ? first == 0 : true);
{
    open nodes(first, vs);
    if (first != 0) {
        nodes_to_llist_lemma(first->next);
    }
    close nodes(first, vs);
}
@*/

struct llist *create_llist()
    //@ requires true;
    //@ ensures llist(result, nil);
{
    struct llist *l = malloc(sizeof(struct llist));
    if (l == 0) abort();
    struct node *n = calloc(1, sizeof(struct node));
    if (n == 0) abort();
    l->first = n;
    l->last = n;
    //@ close nodes(n, nil);
    //@ close llist(l, nil);
    return l;
}

void llist_add(struct llist *list, int x)
    //@ requires llist(list, ?vs);
    //@ ensures llist(list, append(vs, cons(x, nil)));
{
    struct node *l = 0;
    struct node *n = calloc(1, sizeof(struct node));
    if (n == 0) {
        abort();
    }
    l = list->last;
    l->next = n;
    l->value = x;
    list->last = n;
    //@ open llist(list, vs);
    //@ close nodes(n, nil);
    //@ close llist(list, append(vs, cons(x, nil)));
}

void llist_dispose(struct llist *list)
    //@ requires llist(list, _);
    //@ ensures true;
{
    struct node *n = list->first;
    struct node *l = list->last;
    while (n != l)
        //@ invariant nodes(n, ?vs) &*& malloc_block_node(l);
    {
        struct node *next = n->next;
        free(n);
        n = next;
    }
    free(l);
    free(list);
}

struct iter *llist_create_iter(struct llist *l)
    //@ requires llist(l, ?vs);
    //@ ensures iter(result, l, vs);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    f = l->first;
    i->current = f;
    //@ close iter(i, l, vs);
    return i;
}

int iter_next(struct iter *i)
    //@ requires iter(i, ?l, ?vs) &*& vs != nil;
    //@ ensures iter(i, l, tail(vs)) &*& result == head(vs);
{
    struct node *c = i->current;
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ open iter(i, l, vs);
    //@ close iter(i, l, tail(vs));
    return value;
}

void iter_dispose(struct iter *i)
    //@ requires iter(i, ?l, ?vs);
    //@ ensures llist(l, vs);
{
    //@ open iter(i, l, vs);
    free(i);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}