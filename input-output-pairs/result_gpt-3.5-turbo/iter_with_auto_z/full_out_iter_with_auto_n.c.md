```c CODE and SPEC
#include "stdlib.h"
#include "limits.h"

/*@
inductive lseg = lseg(struct node* c1, struct node* c2, list<int> vs);

predicate lseg_sp(struct node* f, struct node* l, list<int> vs) =
  f == l ? vs == nil : l->next |-> ?n &*& l->value |-> ?v &*& malloc_block_node(l) &*& lseg_sp(n, l, ?vs1) &*& vs == cons(v, vs1);

predicate llist(struct llist* list, list<int> vs) =
  list != 0 &*& struct_llist_padding(list) &*& list->first |-> ?f &*& list->last |-> ?l &*& malloc_block_llist(list) &*& lseg(f, l, vs);

struct node* create_llist_helper(struct node* f, struct node* l)
  requires f == l &*& l == 0 ? true : l == 0 ? malloc_block_node(f) &*& f->next |-> _ &*& f->value |-> _ &*& create_llist_helper(f->next, 0) : malloc_block_node(f) &*& f->next |-> ?n &*& f->value |-> ?v &*& create_llist_helper(n, l);
  ensures f == l &*& l == 0 ? lseg_sp(f, l, ?vs) : lseg_sp(f, l, ?vs) &*& head(vs) == v &*& l->next |-> _ &*& l->value |-> _;

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
  //@ close lseg_sp(n, n, nil);
  //@ close llist(l, nil);
  return l;
}

void llist_add(struct llist *list, int x)
  //@ requires llist(list, ?vs) &*& true;
  //@ ensures llist(list, ?vs1) &*& head(vs1) == x;
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
  //@ open llist(list, ?vs0);
  //@ lseg_sp(l, n, ?vs2);
  //@ close lseg_sp(l, n, cons(x, vs2));
  //@ close llist(list, append(vs0, cons(x, vs2)));
}

void llist_append(struct llist *list1, struct llist *list2)
  //@ requires llist(list1, ?vs1) &*& llist(list2, ?vs2);
  //@ ensures llist(list1, ?vs) &*& vs == append(vs1, vs2);
{
  struct node *l1 = list1->last;
  struct node *f2 = list2->first;
  struct node *l2 = list2->last;
  if (f2 == l2) {
    free(l2);
    free(list2);
  } else {
    l1->next = f2->next;
    l1->value = f2->value;
    list1->last = l2;
    free(f2);
    free(list2);
  }
  //@ open llist(list1, ?vs1);
  //@ open llist(list2, ?vs2);
  //@ append_assoc(vs1, cons(?v, ?vs3), vs2);
  //@ close llist(list1, append(vs1, cons(v, vs3)));
}

void llist_dispose(struct llist *list)
  //@ requires llist(list, ?vs);
  //@ ensures true;
{
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  {
    struct node *next = n->next;
    free(n);
    n = next;
  }
  free(l);
  free(list);
}

void main0()
  //@ requires true;
  //@ ensures true;
{
  struct llist *l = create_llist();
  llist_add(l, 10);
  llist_add(l, 20);
  llist_add(l, 30);
  llist_add(l, 40);
  int x1 = llist_removeFirst(l); assert(x1 == 10);
  int x2 = llist_removeFirst(l); assert(x2 == 20);
  llist_dispose(l);
}

int main() 
  //@ requires true;
  //@ ensures true;
{
  struct llist *l1 = create_llist();
  struct llist *l2 = create_llist();
  llist_add(l1, 10);
  llist_add(l1, 20);
  llist_add(l1, 30);
  llist_add(l2, 40);
  llist_add(l2, 50);
  llist_add(l2, 60);
  int x = llist_removeFirst(l2); assert(x == 40);
  llist_append(l1, l2);
  int n = llist_length(l1); assert(n == 5);
  int e0 = llist_lookup(l1, 0); assert(e0 == 10);
  int e1 = llist_lookup(l1, 1); assert(e1 == 20);
  int e2 = llist_lookup(l1, 2); assert(e2 == 30);
  int e3 = llist_lookup(l1, 3); assert(e3 == 50);
  int e4 = llist_lookup(l1, 4); assert(e4 == 60);
  llist_dispose(l1);
  return 0;
}

struct iter {
    struct node *current;
};

struct iter *llist_create_iter(struct llist *l)
  //@ requires llist(l, ?vs);
  //@ ensures result->current |-> ?c &*& lseg(c, _, vs);
{
    struct iter *i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }
    struct node *f = l->first;
    i->current = f;
    //@ close lseg(f, _, vs);
    return i;
}

int iter_next(struct iter *i)
  //@ requires i->current |-> ?c &*& lseg(c, ?n, ?vs) &*& n != 0;
  //@ ensures i->current |-> ?nc &*& lseg(nc, _, tail(vs)) &*& result == head(vs);
{
      struct node *c = i->current;
      int value = c->value;
      struct node *n = c->next;
      i->current = n;
      return value;
}

void iter_dispose(struct iter *i)
  //@ requires i->current |-> _;
  //@ ensures true;
{
    free(i);
}

int main2()
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
```
