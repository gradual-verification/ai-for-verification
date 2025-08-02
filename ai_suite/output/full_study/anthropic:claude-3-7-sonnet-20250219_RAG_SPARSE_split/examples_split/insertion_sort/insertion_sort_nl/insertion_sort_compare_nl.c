// Definition of a singly linked list node holding an integer value
struct list_node {
  int value;
  struct list_node* next;
};

/*@
// Define a predicate for a list node
predicate list_node(struct list_node* n; int value, struct list_node* next) =
    n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The compare function compares the integer values of two linked list nodes.

@param n0 - pointer to the first node.
@param n1 - pointer to the second node.
@return -1 if n0's value < n1's value,
 *          1 if n0's value > n1's value,
 *          0 if equal.

It also makes sure that the values of the nodes are not modified during comparison.
*/
/*@
// Function contract
requires list_node(n0, ?v0, ?next0) &*& list_node(n1, ?v1, ?next1);
ensures list_node(n0, v0, next0) &*& list_node(n1, v1, next1) &*& 
        (v0 < v1 ? result == -1 : (v0 > v1 ? result == 1 : result == 0));
@*/
static int compare(struct list_node* n0, struct list_node* n1)
{
  /*@ open list_node(n0, v0, next0); @*/
  /*@ open list_node(n1, v1, next1); @*/
  
  if (n0->value < n1->value) {
    /*@ close list_node(n0, v0, next0); @*/
    /*@ close list_node(n1, v1, next1); @*/
    return -1;
  } else if (n0->value > n1->value) {
    /*@ close list_node(n0, v0, next0); @*/
    /*@ close list_node(n1, v1, next1); @*/
    return 1;
  } else {
    /*@ close list_node(n0, v0, next0); @*/
    /*@ close list_node(n1, v1, next1); @*/
    return 0;
  }
}