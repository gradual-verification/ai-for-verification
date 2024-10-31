```c
#include "stdlib.h"
#include "limits.h"  // For INT_MAX

struct node {
  struct node *next;
  int value;
};

/*@
predicate lseg(struct node *from, struct node *to; list<int> vs) =
    from == to ?
        vs == nil
    :
        from->value |-> ?v &*& from->next |-> ?n &*& malloc_block_node(from) &*& lseg(n, to, ?vs0) &*& vs == cons(v, vs0);

predicate llist(struct llist *l; list<int> vs) =
    l->first |-> ?f &*& l->last |-> ?la &*& malloc_block_llist(l) &*& lseg(f, la, vs) &*& la->next |-> _ &*& la->value |-> _ &*& malloc_block_node(la);
@*/

struct llist {
  struct node *first;
  struct node *last;
};

/*@
requires true;
ensures llist(result, nil);
@*/
struct llist *create_llist()
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  //@ malloc_block_llist(l);
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ malloc_block_node(n);
  l->first = n;
  l->last = n;
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

/*@
requires llist(list, ?vs);
ensures llist(list, append(vs, cons(x, nil)));
@*/
void llist_add(struct llist *list, int x)
{
  //@ open llist(list, vs);
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  //@ malloc_block_node(n);
  //@ open lseg(list->first, list->last, vs);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close lseg(l->next, list->last, nil);
  //@ close lseg(list->first, list->last, append(vs, cons(x, nil)));
  //@ close llist(list, append(vs, cons(x, nil)));
}

/*@
requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
ensures llist(list1, append(vs1, vs2));
@*/
void llist_append(struct llist *list1, struct llist *list2)
{
  //@ open llist(list1, vs1);
  //@ open llist(list2, vs2);
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    free(l2);
    //@ malloc_block_node(l2);
    free(list2);
    //@ malloc_block_llist(list2);
    //@ close lseg(list1->first, list1->last, vs1);
    //@ close llist(list1, vs1);
  } else {
    //@ open lseg(f2, l2, vs2);
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    //@ malloc_block_node(f2);
    free(list2);
    //@ malloc_block_llist(list2);
    //@ close lseg(l1, l2, vs2);
    //@ append_assoc(vs1, cons(_), vs2);
    //@ close lseg(list1->first, l2, append(vs1, vs2));
    //@ close llist(list1, append(vs1, vs2));
  }
}

/*@
requires llist(list, ?vs);
ensures true;
@*/
void llist_dispose(struct llist *list)
{
  //@ open llist(list, ?vs);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open lseg(n, l, vs);
  while (n != l)
  /*@
  invariant lseg(n, l, ?vs0) &*& lseg(list->first, n, ?vs_prefix) &*& vs == append(vs_prefix, vs0);
  @*/
  {
    struct node *next = n->next;
    //@ open lseg(n, next, cons(n->value, nil));
    free(n);
    //@ malloc_block_node(n);
    n = next;
  }
  //@ open lseg(l, l, nil);
  free(l);
  //@ malloc_block_node(l);
  free(list);
  //@ malloc_block_llist(list);
}

/*@
requires llist(list, ?vs);
ensures llist(list, vs) &*& result == length(vs);
@*/
int llist_length(struct llist *list)
{
  //@ open llist(list, ?vs);
  struct node *f = list->first;
  struct node *n = f;
  struct node *l = list->last;
  int c = 0;
  //@ open lseg(n, l, vs);
  while (n != l)
  /*@
  invariant lseg(n, l, ?vs_rest) &*& lseg(f, n, ?vs_prefix) &*& vs == append(vs_prefix, vs_rest) &*& c == length(vs_prefix);
  @*/
  {
    struct node *next = n->next;
    n = next;
    if (c == INT_MAX) abort();
    c = c + 1;
  }
  //@ close lseg(n, l, nil);
  //@ close lseg(f, l, vs);
  //@ close llist(list, vs);
  return c;
}

/*@
requires llist(list, ?vs) &*& 0 <= index &*& index < length(vs);
ensures llist(list, vs) &*& result == nth(index, vs);
@*/
int llist_lookup(struct llist *list, int index)
{
  //@ open llist(list, ?vs);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open lseg(n, l, vs);
  int i = 0;
  while (i < index)
  /*@
  invariant lseg(n, l, ?vs_rest) &*& lseg(list->first, n, ?vs_prefix) &*& vs == append(vs_prefix, vs_rest) &*& i == length(vs_prefix);
  @*/
  {
    struct node *next = n->next;
    n = next;
    i = i + 1;
  }
  int value = n->value;
  //@ close lseg(n, l, _);
  //@ close lseg(list->first, l, vs);
  //@ close llist(list, vs);
  return value;
}

/*@
requires llist(l, ?vs) &*& vs != nil;
ensures llist(l, tail(vs)) &*& result == head(vs);
@*/
int llist_removeFirst(struct llist *l)
{
  //@ open llist(l, ?vs);
  struct node *nf = l->first;
  //@ open lseg(nf, l->last, vs);
  struct node *nfn = nf->next;
  int nfv = nf->value;
  free(nf);
  //@ malloc_block_node(nf);
  l->first = nfn;
  //@ close lseg(nfn, l->last, tail(vs));
  //@ close llist(l, tail(vs));
  return nfv;
}

/*@
requires true;
ensures true;
@*/
void main0()
{
  struct llist *l = create_llist();
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  int x1 = llist_removeFirst(l);
  //@ assert x1 == 10;
  int x2 = llist_removeFirst(l);
  //@ assert x2 == 20;
  llist_dispose(l);
}

/*@
requires true;
ensures true;
@*/
int main() 
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2);
  //@ assert x == 40;
  llist_append(l1, l2);
  int n = llist_length(l1);
  //@ assert n == 5;
  int e0 = llist_lookup(l1, 0);
  //@ assert e0 == 10;
  int e1 = llist_lookup(l1, 1);
  //@ assert e1 == 20;
  int e2 = llist_lookup(l1, 2);
  //@ assert e2 == 30;
  int e3 = llist_lookup(l1, 3);
  //@ assert e3 == 50;
  int e4 = llist_lookup(l1, 4);
  //@ assert e4 == 60;
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

/*@
predicate iter(struct iter *i; struct node *current) =
    i->current |-> current &*& malloc_block_iter(i);
@*/

/*@
requires llist(l, ?vs);
ensures llist(l, vs) &*& iter(result, l->first);
@*/
struct iter *llist_create_iter(struct llist *l)
{
    struct iter *i = malloc(sizeof(struct iter));
    if (i == 0) abort();
    //@ malloc_block_iter(i);
    i->current = l->first;
    //@ close iter(i, l->first);
    return i;
}

/*@
requires iter(i, ?current) &*& current != 0 &*& current->value |-> ?v &*& current->next |-> ?n &*& malloc_block_node(current);
ensures iter(i, n) &*& current->value |-> v &*& current->next |-> n &*& malloc_block_node(current) &*& result == v;
@*/
int iter_next(struct iter *i)
{
    //@ open iter(i, current);
    struct node *c = i->current;
    int value = c->value;
    i->current = c->next;
    //@ close iter(i, c->next);
    return value;
}

/*@
requires iter(i, _);
ensures true;
@*/
void iter_dispose(struct iter *i)
{
    //@ open iter(i, _);
    free(i);
    //@ malloc_block_iter(i);
}

/*@
requires true;
ensures true;
@*/
int main2()
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    int i1e1 = iter_next(i1); //@ assert i1e1 == 5;
    int i2e1 = iter_next(i2); //@ assert i2e1 == 5;
    int i1e2 = iter_next(i1); //@ assert i1e2 == 10;
    int i2e2 = iter_next(i2); //@ assert i2e2 == 10;
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}
```
