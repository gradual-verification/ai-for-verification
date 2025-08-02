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
// Define a predicate for a linked list node
predicate node(struct node *n, int value, struct node *next) =
    n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);

// Define a predicate for a list segment
predicate lseg(struct node *from, struct node *to, list<int> values) =
    from == to ?
        values == nil
    :
        node(from, ?v, ?next) &*& lseg(next, to, ?tail) &*& values == cons(v, tail);

// Define a predicate for the linked list
predicate llist(struct llist *l, list<int> values) =
    l->first |-> ?first &*& l->last |-> ?last &*& 
    lseg(first, last, values) &*& 
    node(last, _, 0) &*& 
    malloc_block_llist(l);

// Define a predicate for an iterator
predicate iter(struct iter *i, struct llist *l, struct node *current) =
    i->current |-> current &*& malloc_block_iter(i);

// Define a lemma to help with list segment manipulation
lemma void lseg_add(struct node *first, struct node *last, int value)
    requires lseg(first, last, ?values) &*& node(last, value, ?next);
    ensures lseg(first, next, append(values, cons(value, nil)));
{
    open lseg(first, last, values);
    if (first == last) {
        close lseg(next, next, nil);
    } else {
        lseg_add(first->next, last, value);
    }
    close lseg(first, next, append(values, cons(value, nil)));
}
@*/

/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
//@ requires true;
//@ ensures result == 0 ? true : llist(result, nil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close node(n, 0, 0);
  //@ close lseg(n, n, nil);
  //@ close llist(l, nil);
  return l;
}


/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
//@ requires llist(list, ?values);
//@ ensures llist(list, append(values, cons(x, nil)));
{
  //@ open llist(list, values);
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  //@ open node(l, _, _);
  l->next = n;
  l->value = x;
  list->last = n;
  //@ close node(n, 0, 0);
  //@ lseg_add(list->first, l, x);
  //@ close llist(list, append(values, cons(x, nil)));
}


/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
//@ requires llist(list, ?values);
//@ ensures true;
{
  //@ open llist(list, values);
  struct node *n = list->first;
  struct node *l = list->last;
  while (n != l)
  //@ invariant lseg(n, l, ?remaining) &*& node(l, _, 0);
  {
    //@ open lseg(n, l, remaining);
    //@ open node(n, _, _);
    struct node *next = n->next;
    free(n);
    n = next;
  }
  //@ open lseg(l, l, _);
  //@ open node(l, _, _);
  free(l);
  free(list);
}


/**
 * Description:
The `llist_create_iter` function creates an iterator for a given linked list,
which is located at the first node of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param l - Pointer to the linked list structure.
@return - The created iterator pointing to the first node of linked list.
*/
struct iter *llist_create_iter(struct llist *l)
//@ requires [?f]llist(l, ?values);
//@ ensures [f]llist(l, values) &*& iter(result, l, l->first);
{
    struct iter *i = 0;
    struct node *f = 0;
    //@ open [f]llist(l, values);
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    f = l->first;
    i->current = f;
    //@ close iter(i, l, f);
    //@ close [f]llist(l, values);
    return i;
}


/***
 * Description:
The `iter_next` function returns the value of the current node of the iterator
and moves the iterator to the next node. It requires that the iterator is not at the end of the linked list.
Note that the linked list cannot be modified unless we free the iterator.

@param i - Iterator of the linked list.
@return - The value of the original node that the iterator is at.
*/
int iter_next(struct iter *i)
//@ requires iter(i, ?l, ?current) &*& [?f]llist(l, ?values) &*& current != l->last;
//@ ensures iter(i, l, current->next) &*& [f]llist(l, values) &*& result == current->value;
{
    //@ open iter(i, l, current);
    //@ open [f]llist(l, values);
    //@ open [f]lseg(l->first, l->last, values);
    struct node *c = i->current;
    //@ assert c == current;
    //@ open [f]node(c, ?value, ?next);
    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    //@ close [f]node(c, value, next);
    //@ close [f]lseg(l->first, l->last, values);
    //@ close [f]llist(l, values);
    //@ close iter(i, l, next);
    return value;
}


/***
 * Description:
The `iter_dispose` function deallocates the memory associated with the iterator.

@param i - Iterator of the linked list
*/
void iter_dispose(struct iter *i)
//@ requires iter(i, ?l, ?current);
//@ ensures true;
{
    //@ open iter(i, l, current);
    free(i);
}


// TODO: make this function pass the verification
/***
 * Description:
The `main` function tests the functions of llist by creating a linked list,
adding elements to it, creating 2 iterators and iterating over the linked list,
and finally disposing of the iterators and the list.
*/
int main()
//@ requires true;
//@ ensures true;
{
    struct llist *l = create_llist();
    llist_add(l, 5);
    llist_add(l, 10);
    llist_add(l, 15);
    
    //@ assert llist(l, cons(5, cons(10, cons(15, nil))));
    
    struct iter *i1 = llist_create_iter(l);
    struct iter *i2 = llist_create_iter(l);
    
    //@ open [1/2]llist(l, _);
    //@ assert i1->current == l->first;
    //@ assert i2->current == l->first;
    //@ close [1/2]llist(l, _);
    
    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    
    iter_dispose(i1);
    iter_dispose(i2);
    llist_dispose(l);
    return 0;
}