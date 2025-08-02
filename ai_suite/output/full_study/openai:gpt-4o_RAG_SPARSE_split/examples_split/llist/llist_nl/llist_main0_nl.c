#include "stdlib.h"

/*@
inductive llist = lnil | lcons(int, llist);

fixpoint llist lappend(llist xs, llist ys) {
    switch (xs) {
        case lnil: return ys;
        case lcons(h, t): return lcons(h, lappend(t, ys));
    }
}

predicate nodes(struct node *n, llist values) =
    n == 0 ?
        values == lnil
    :
        n->next |-> ?next &*& n->value |-> ?value &*& malloc_block_node(n) &*&
        nodes(next, ?values0) &*&
        values == lcons(value, values0);

predicate llist(struct llist *l, llist values) =
    l->first |-> ?first &*& l->last |-> ?last &*& malloc_block_llist(l) &*&
    nodes(first, ?values0) &*&
    last->next |-> 0 &*&
    values == lappend(values0, lcons(0, lnil));
@*/

/***
 * Description:
The create_llist function allocates an empty linked list with a node as both the first and last of the linked list.

It makes sure that the return value is an empty list. 
*/
struct llist *create_llist()
    //@ requires true;
    //@ ensures llist(result, lcons(0, lnil));
{
    struct llist *l = malloc(sizeof(struct llist));
    if (l == 0) abort();
    struct node *n = calloc(1, sizeof(struct node));
    if (n == 0) abort();
    l->first = n;
    l->last = n;
    //@ close nodes(n, lcons(0, lnil));
    //@ close llist(l, lcons(0, lnil));
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
    //@ ensures llist(list, lappend(values, lcons(x, lnil)));
{
    struct node *l = 0;
    struct node *n = calloc(1, sizeof(struct node));
    if (n == 0) {
        abort();
    }
    //@ open llist(list, values);
    l = list->last;
    l->next = n;
    l->value = x;
    list->last = n;
    //@ close nodes(n, lcons(0, lnil));
    //@ close llist(list, lappend(values, lcons(x, lnil)));
}

/***
 * Description:
The llist_dispose function frees a list by iteratively freeing the nodes.

@param list: a single linked list to be freed
*/
void llist_dispose(struct llist *list)
    //@ requires llist(list, lcons(0, lnil));
    //@ ensures true;
{
    //@ open llist(list, lcons(0, lnil));
    struct node *n = list->first;
    struct node *l = list->last;
    while (n != l)
        //@ invariant nodes(n, ?values);
    {
        //@ open nodes(n, _);
        struct node *next = n->next;
        free(n);
        n = next;
    }
    //@ open nodes(l, _);
    free(l);
    free(list);
}

/***
 * Description:
The `llist_removeFirst` function removes the first node from the non-empty linked list and returns its value.

@param l - Pointer to the non-empty linked list structure.
@return - The value of the first node that is removed from the linked list.
*/
int llist_removeFirst(struct llist *l)
    //@ requires llist(l, lcons(?x, ?values)) &*& x != 0;
    //@ ensures llist(l, values) &*& result == x;
{
    //@ open llist(l, lcons(x, values));
    struct node *nf = l->first;
    //@ open nodes(nf, _);
    struct node *nfn = nf->next;
    int nfv = nf->value;
    free(nf);
    l->first = nfn;
    //@ close llist(l, values);
    return nfv;
}

// TODO: make this function pass the verification
/***
 * Description:
The `main0` function tests the `llist_add` and `llist_removeFirst` functions by creating a linked list,
adding elements to it, removing the first two elements, and then disposing of the list.
It asserts that the removed elements have the correct values.
*/
void main0()
    //@ requires true;
    //@ ensures true;
{
    struct llist *l = create_llist();
    llist_add(l, 10);
    llist_add(l, 20);
    llist_add(l, 30);
    llist_add(l, 40);
    int x1 = llist_removeFirst(l);
    assert(x1 == 10);
    int x2 = llist_removeFirst(l);
    assert(x2 == 20);
    llist_dispose(l);
}