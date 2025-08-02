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

//@ predicate nodes(struct node* n, list<void*> vs) =
//@   n == 0 ? vs == nil : n->value |-> ?v &*& n->next |-> ?next &*& malloc_block_node(n) &*& nodes(next, ?vs0) &*& vs == cons(v, vs0);

//@ predicate is_equals(equals* eq) = true;

// TODO: make this function pass the verification
/*list_contains() function
-params: struct node* n, void* v, equals* eq
-description: check if the list starting on n contains the element v.

It requires that n is the starting node of the list, eq is a equal function, which can be applied on each element in the list. 
It ensures that the list is unchanged, and the return value is the result of checking whether any element in the list is equal to v.
*/
bool list_contains(struct node* n, void* v, equals* eq) 
    //@ requires nodes(n, ?vs) &*& is_equals(eq) &*& [_]is_equals(eq);
    //@ ensures nodes(n, vs) &*& result == mem(v, vs);
{
    //@ open nodes(n, vs);
    if(n == 0) {
        //@ close nodes(n, vs);
        return false;
    } else {
        bool cont = eq(v, n->value);
        if(cont) {
            //@ close nodes(n, vs);
            return true;
        } else {
            bool result = list_contains(n->next, v, eq);
            //@ close nodes(n, vs);
            return result;
        }
    }
}