#include "stdlib.h"
//@ #include "list.gh"

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
// A list segment from 'from' up to (but not including) 'to'.
// It abstractly represents the list of integer values 'vs'.
predicate lseg(struct node* from, struct node* to; list<int> vs) =
    from == to ?
        vs == nil
    :
        from != 0 &*&
        from->next |-> ?next &*&
        from->value |-> ?v &*&
        malloc_block_node(from) &*&
        lseg(next, to, ?rest) &*&
        vs == cons(v, rest);

// An llist is a list segment from 'first' to 'last', where 'last' is a dummy node.
predicate llist(struct llist* list; list<int> vs) =
    list->first |-> ?first &*&
    list->last |-> ?last &*&
    malloc_block_llist(list) &*&
    lseg(first, last, vs) &*&
    last != 0 &*&
    last->next |-> 0 &*&
    last->value |-> _ &*& // The value of the dummy node is not specified.
    malloc_block_node(last);

// Lemma to prove that updating the tail of an lseg and linking a new node
// corresponds to appending an element to the abstract list.
lemma void lseg_add_node(struct node* from, struct node* to)
    requires lseg(from, to, ?vs) &*& to != 0 &*& to->next |-> ?next &*& to->value |-> ?v &*& malloc_block_node(to);
    ensures lseg(from, next, append(vs, cons(v, nil)));
{
    open lseg(from, to, vs);
    if (from == to) {
        close lseg(next, next, nil);
    } else {
        lseg_add_node(from->next, to);
    }
    close lseg(from, next, append(vs, cons(v, nil)));
}
@*/


// TODO: make this function pass the verification
/***
 * Description:
The list_add function adds an element to the end of the linked list,

@param list: a single linked list
@param x: the element to be added

It makes sure that the list has added x as its last element.
*/
void llist_add(struct llist *list, int x)
    //@ requires llist(list, ?vs);
    //@ ensures llist(list, append(vs, cons(x, nil)));
{
    //@ open llist(list, vs);
    //@ assert list->first |-> ?first;
    struct node *l = 0;
    struct node *n = calloc(1, sizeof(struct node));
    if (n == 0) {
        abort();
    }
    //@ assert n->next |-> 0 &*& n->value |-> 0 &*& malloc_block_node(n);

    l = list->last;
    l->next = n;
    l->value = x;
    list->last = n;

    //@ lseg_add_node(first, l);

    //@ close llist(list, append(vs, cons(x, nil)));
}