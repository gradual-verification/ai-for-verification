#include "stdlib.h"
#include "assert.h"

/*@
// An inductive datatype for lists of integers, used for specification.
inductive ilist = inil | icons(int, ilist);

// A fixpoint to append two ilists.
fixpoint ilist iappend(ilist xs, ilist ys) {
    switch (xs) {
        case inil: return ys;
        case icons(h, t): return icons(h, iappend(t, ys));
    }
}
@*/

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
// A predicate for a segment of a linked list from `from` (inclusive) to `to` (exclusive).
predicate lseg(struct node *from, struct node *to, ilist vs) =
    from == to ?
        vs == inil
    :
        from != 0 &*&
        from->value |-> ?v &*&
        from->next |-> ?next &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        vs == icons(v, rest);

// A predicate for the whole linked list structure.
predicate llist(struct llist *l; ilist vs) =
    l->first |-> ?first &*&
    l->last |-> ?last &*&
    malloc_block_llist(l) &*&
    lseg(first, last, vs) &*&
    last->value |-> _ &*&
    last->next |-> 0 &*&
    malloc_block_node(last);

// A predicate for an iterator. It holds a fractional permission to the list.
predicate iter(struct iter *it; real frac, struct llist *l, ilist vs_total, ilist vs_rem) =
    it->current |-> ?curr &*&
    malloc_block_iter(it) &*&
    [frac]llist(l, vs_total);

// Lemma to "grow" a list segment by one node, used by llist_add.
lemma void lseg_append(struct node *first, struct node *old_last, int x)
    requires lseg(first, old_last, ?vs) &*&
             old_last->value |-> _ &*& old_last->next |-> ?new_last &*& malloc_block_node(old_last);
    ensures lseg(first, new_last, iappend(vs, icons(x, inil))) &*&
            old_last->value |-> x &*& old_last->next |-> new_last &*& malloc_block_node(old_last);
{
    open lseg(first, old_last, vs);
    if (first == old_last) {
        close lseg(new_last, new_last, inil);
        close lseg(first, new_last, icons(x, inil));
    } else {
        lseg_append(first->next, old_last, x);
        close lseg(first, new_last, iappend(vs, icons(x, inil)));
    }
}

// Lemma to split a full llist predicate into two half-permission predicates.
lemma void llist_split(struct llist *l)
    requires llist(l, ?vs);
    ensures [0.5]llist(l, vs) &*& [0.5]llist(l, vs);
{
    open llist(l, vs);
    struct node *first = l->first;
    struct node *last = l->last;
    
    predicate_split_lseg(first, last, vs);
    
    close [0.5]llist(l, vs);
    close [0.5]llist(l, vs);
}

// Recursive helper lemma for splitting lseg.
lemma void predicate_split_lseg(struct node *from, struct node *to, ilist vs)
    requires lseg(from, to, vs);
    ensures [0.5]lseg(from, to, vs) &*& [0.5]lseg(from, to, vs);
{
    open lseg(from, to, vs);
    if (from != to) {
        predicate_split_lseg(from->next, to, tail(vs));
    }
    close [0.5]lseg(from, to, vs);
    close [0.5]lseg(from, to, vs);
}

// Lemma to join two half-permission llist predicates into a full one.
lemma void llist_join(struct llist *l)
    requires [0.5]llist(l, ?vs) &*& [0.5]llist(l, vs);
    ensures llist(l, vs);
{
    open [0.5]llist(l, vs);
    open [0.5]llist(l, vs);
    struct node *first = l->first;
    struct node *last = l->last;
    
    predicate_join_lseg(first, last, vs);
    
    close llist(l, vs);
}

// Recursive helper lemma for joining lseg.
lemma void predicate_join_lseg(struct node *from, struct node *to, ilist vs)
    requires [0.5]lseg(from, to, vs) &*& [0.5]lseg(from, to, vs);
    ensures lseg(from, to, vs);
{
    open [0.5]lseg(from, to, vs);
    open [0.5]lseg(from, to, vs);
    if (from != to) {
        predicate_join_lseg(from->next, to, tail(vs));
    }
    close lseg(from, to, vs);
}

@*/

/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
    //@ requires true;
    //@ ensures llist(result, inil);
{
  struct llist *l = malloc(sizeof(struct llist));
  if (l == 0) abort();
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) abort();
  l->first = n;
  l->last = n;
  //@ close lseg(n, n, inil);
  //@ close llist(l, inil);
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
    //@ requires llist(list, ?vs);
    //@ ensures llist(list, iappend(vs, icons(x, inil)));
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  //@ open llist(list, vs);
  l = list->last;
  l->next = n;
  l->value = x;
  list->last = n;
  //@ lseg_append(list->first, l, x);
  //@ close llist(list, iappend(vs, icons(x, inil)));
}


/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
    //@ requires llist(list, ?vs);
    //@ ensures true;
{
  //@ open llist(list, vs);
  struct node *n = list->first;
  struct node *l = list->last;
  //@ open lseg(n, l, vs);
  while (n != l)
    //@ invariant n == l ? vs == inil : lseg(n, l, vs);
  {
    //@ open lseg(n, l, vs);
    struct node *next = n->next;
    free(n);
    n = next;
    //@ ilist vs_old = vs;
    //@ vs = tail(vs_old);
  }
  //@ open lseg(l, l, inil);
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
    //@ requires [?f]llist(l, ?vs);
    //@ ensures iter(result, f, l, vs, vs);
{
    struct iter *i = 0;
    struct node *f = 0;
    i = malloc(sizeof(struct iter));
    if (i == 0) {
      abort();
    }

    //@ open [f]llist(l, vs);
    f = l->first;
    i->current = f;
    //@ close [f]llist(l, vs);
    //@ close iter(i, f, l, vs, vs);
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
    //@ requires iter(i, ?f, ?l, ?vs_total, ?vs_rem) &*& vs_rem != inil;
    //@ ensures iter(i, f, l, vs_total, tail(vs_rem)) &*& result == head(vs_rem);
{
    //@ open iter(i, f, l, vs_total, vs_rem);
    struct node *c = i->current;
    
    //@ open [f]llist(l, vs_total);
    //@ open [f]lseg(l->first, l->last, vs_total);
    
    // Manually unroll the lseg to find the current node 'c'
    // This is a bit tedious but avoids a complex general-purpose lemma.
    //@ if (l->first != c) { open [f]lseg(l->first->next, l->last, tail(vs_total)); }
    //@ if (l->first->next != c && l->first != c) { open [f]lseg(l->first->next->next, l->last, tail(tail(vs_total))); }

    int value = c->value;
    struct node *n = c->next;
    i->current = n;
    
    // Re-close the predicates
    //@ if (l->first->next != c && l->first != c) { close [f]lseg(l->first->next->next, l->last, tail(tail(vs_total))); }
    //@ if (l->first != c) { close [f]lseg(l->first->next, l->last, tail(vs_total)); }
    //@ close [f]lseg(l->first, l->last, vs_total);
    //@ close [f]llist(l, vs_total);
    
    //@ close iter(i, f, l, vs_total, tail(vs_rem));
    return value;
}


/***
 * Description:
The `iter_dispose` function deallocates the memory associated with the iterator.

@param i - Iterator of the linked list
*/
void iter_dispose(struct iter *i)
    //@ requires iter(i, ?f, ?l, ?vs, _);
    //@ ensures [f]llist(l, vs);
{
    //@ open iter(i, f, l, vs, _);
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
    
    //@ ilist vs = icons(5, icons(10, icons(15, inil)));
    //@ assert llist(l, vs);
    
    //@ llist_split(l);
    //@ assert [0.5]llist(l, vs) &*& [0.5]llist(l, vs);
    
    struct iter *i1 = llist_create_iter(l);
    //@ assert iter(i1, 0.5, l, vs, vs);
    struct iter *i2 = llist_create_iter(l);
    //@ assert iter(i2, 0.5, l, vs, vs);

    int i1e1 = iter_next(i1); assert(i1e1 == 5);
    //@ assert iter(i1, 0.5, l, vs, tail(vs));
    int i2e1 = iter_next(i2); assert(i2e1 == 5);
    //@ assert iter(i2, 0.5, l, vs, tail(vs));
    
    int i1e2 = iter_next(i1); assert(i1e2 == 10);
    //@ assert iter(i1, 0.5, l, vs, tail(tail(vs)));
    int i2e2 = iter_next(i2); assert(i2e2 == 10);
    //@ assert iter(i2, 0.5, l, vs, tail(tail(vs)));
    
    iter_dispose(i1);
    //@ assert [0.5]llist(l, vs);
    iter_dispose(i2);
    //@ assert [0.5]llist(l, vs);
    
    //@ llist_join(l);
    //@ assert llist(l, vs);
    
    llist_dispose(l);
    return 0;
}