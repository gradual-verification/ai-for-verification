#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};


/*equals() function
-params: void* v1, void* v2
-description: checks whether two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* v1, void* v2);

/*@
// Predicate to represent a linked list
predicate nodes(struct node* n, list<void*> values) =
    n == 0 ?
        values == nil
    :
        n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*&
        nodes(next, ?tail) &*& values == cons(v, tail);

// Predicate family for the equals function
predicate_family equals_pre(void* equals_func)(void* v1, void* v2);
predicate_family equals_post(void* equals_func)(void* v1, void* v2, bool result);

// Contract for the equals function type
@*/
typedef bool equals(void* v1, void* v2);
    //@ requires true;
    //@ ensures result ? v1 == v2 : v1 != v2;

/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, which can be applied on each element in the list. 
It ensures that the list is unchanged, and the return value is the result of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq) 
    //@ requires nodes(n, ?values) &*& is_equals(eq) == true;
    //@ ensures nodes(n, values) &*& result == mem(v, values);
{
    if(n == 0) {
        return false;
    } else {
        //@ open nodes(n, values);
        bool cont = eq(v, n->value);
        if(cont) {
            //@ assert n->next |-> ?next;
            //@ assert nodes(next, ?tail);
            list_contains(n->next, v, eq); // hack: just to get my_post for the remaining elements
            //@ close nodes(n, values);
            return true;
        } else {
            //@ assert n->next |-> ?next;
            //@ assert nodes(next, ?tail);
            cont = list_contains(n->next, v, eq);
            //@ close nodes(n, values);
            return cont;
        }
    }
}