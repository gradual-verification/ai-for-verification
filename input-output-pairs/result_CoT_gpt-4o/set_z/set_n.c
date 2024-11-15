#include "stdlib.h"
#include "stdbool.h"
//@ #include "maps.gh"

/*@
predicate node(struct node* node; void* val, struct node* next) =
    node != 0 &*& 
    node->val |-> val &*& 
    node->next |-> next;

predicate set(struct set* set; list<void*> elements) =
    set != 0 &*& 
    set->head |-> ?head &*& 
    nodes(head, elements);

predicate nodes(struct node* node; list<void*> elements) =
    node == 0 ?
        elements == nil
    :
        node(node, ?val, ?next) &*& 
        nodes(next, ?rest) &*& 
        elements == cons(val, rest);

fixpoint bool contains<t>(list<t> lst, t x) {
    switch(lst) {
        case nil: return false;
        case cons(h, t): return h == x ? true : contains(t, x);
    }
}
@*/

/*** 
 * Description:
The create_set function creates a new, empty set.

@param - None.
@requires - No specific preconditions.
@ensures - Returns a pointer to a newly allocated set if successful, or 0 if memory allocation fails. The set is initially empty.
*/
//@ requires emp;
//@ ensures result == 0 ? emp : set(result, nil);
struct set* create_set()
{
    struct set* set = malloc(sizeof(struct set));
    if(set == 0) return 0;
    set->head = 0;
    //@ close nodes(0, nil);
    //@ close set(set, nil);
    return set;
}

/*** 
 * Description:
The set_add function adds a new element to the set.

@param set - A pointer to the set.
@param x - A pointer to the element to be added.
@requires - The set must be valid and x must not already be in the set.
@ensures - The set is updated to include x, and the size of the set is incremented by one.
*/
//@ requires set(set, ?elements);
//@ ensures set(set, cons(x, elements));
void set_add(struct set* set, void* x)
{
    struct node* n = malloc(sizeof(struct node));
    if(n == 0) abort();
    n->next = set->head;
    n->val = x;
    set->head = n;
    //@ close node(n, x, set->head);
    //@ close set(set, cons(x, elements));
}

/***
 * Description: 
The set_contains function checks whether a given element is present in the set.

@param set - A pointer to the set.
@param x - A pointer to the element to check for.
@requires - The set must be valid.
@ensures - Returns true if x is present in the set, otherwise returns false. The set remains unchanged.
*/
//@ requires set(set, ?elements);
//@ ensures set(set, elements) &*& result == contains(elements, x);
bool set_contains(struct set* set, void* x)
{
    struct node* curr = set->head;
    bool found = false;
    
    //@ open nodes(curr, elements);
    //@ open set(set, elements);
    
    while(curr != 0 && !found) 
    //@ invariant nodes(curr, ?elems) &*& elems == elements && contains(elems, x) == found;
    {
        //@ open node(curr, ?val, ?next);
        if(curr->val == x) {
            found = true;
        }
        curr = curr->next;
        //@ open nodes(curr, _);
    }
    //@ close nodes(curr, ?rest);
    
    return found;
}

/***
 * Description:
The set_dispose function disposes of the set by freeing all allocated memory.

@param set - A pointer to the set to be disposed of.
@requires - The set must be valid.
@ensures - All memory associated with the set is freed, and the set is no longer valid.
*/
//@ requires set(set, ?elements);
//@ ensures emp;
void set_dispose(struct set* set)
{
    struct node* curr = set->head;
    //@ open set(set, elements);
    while(curr != 0) 
    //@ invariant nodes(curr, _);
    {
        //@ open node(curr, _, ?next);
        struct node* nxt = curr->next;
        free(curr);
        curr = nxt;
    }
    //@ open nodes(curr, _);
    free(set);
}

/***
* Description:
The main function demonstrates the use of the set data structure.

@param - None.
@requires - No specific preconditions.
@ensures - Adds elements to the set, checks for their existence, and then disposes of the set.
*/
//@ requires emp;
//@ ensures emp;
int main() 
{
    struct set* set = create_set();
    if(set == 0) return 0;
    set_add(set, (void*) 1);
    set_add(set, (void*) 2);
    set_add(set, (void*) 3);
    bool cnt = set_contains(set, (void*) 1);
    assert(cnt);
    set_dispose(set);
    return 0;
}
