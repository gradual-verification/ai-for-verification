#include "stdlib.h"

struct node {
  void* value;
  struct node* next;
};

// specific to cell

struct cell {
  int val;
};

/*@
// Predicate for a cell structure
predicate cell(struct cell* c, int value) =
    c->val |-> value &*& malloc_block_cell(c);

// Predicate for a node structure
predicate node(struct node* n, void* value, struct node* next) =
    n->value |-> value &*& n->next |-> next &*& malloc_block_node(n);
@*/

// TODO: make this function pass the verification
/*equals() function
-params: void* x1, void* x2
-description: checks whether the elements of two pointers are equal. It doesn't have a concrete definition.
*/
typedef bool equals(void* x1, void* x2);
    /*@
    requires x1 != 0 &*& x2 != 0 &*&
             [?f1]cell(x1, ?v1) &*& [?f2]cell(x2, ?v2);
    ensures [f1]cell(x1, v1) &*& [f2]cell(x2, v2) &*& result == (v1 == v2);
    @*/

/*@
// Implementation of the equals function for cells
lemma void equals_cell_refl(struct cell* c, int v)
    requires [?f]cell(c, v);
    ensures [f]cell(c, v) &*& true == (v == v);
{
    // Reflexivity of equality
}

lemma void equals_cell_symm(struct cell* c1, struct cell* c2, int v1, int v2)
    requires [?f1]cell(c1, v1) &*& [?f2]cell(c2, v2);
    ensures [f1]cell(c1, v1) &*& [f2]cell(c2, v2) &*& (v1 == v2) == (v2 == v1);
{
    // Symmetry of equality
}

lemma void equals_cell_trans(struct cell* c1, struct cell* c2, struct cell* c3, int v1, int v2, int v3)
    requires [?f1]cell(c1, v1) &*& [?f2]cell(c2, v2) &*& [?f3]cell(c3, v3) &*& v1 == v2 &*& v2 == v3;
    ensures [f1]cell(c1, v1) &*& [f2]cell(c2, v2) &*& [f3]cell(c3, v3) &*& v1 == v3;
{
    // Transitivity of equality
}
@*/

// Implementation of the equals function for cells
bool equals_cell(void* x1, void* x2)
    //@ requires x1 != 0 &*& x2 != 0 &*& [?f1]cell(x1, ?v1) &*& [?f2]cell(x2, ?v2);
    //@ ensures [f1]cell(x1, v1) &*& [f2]cell(x2, v2) &*& result == (v1 == v2);
{
    struct cell* c1 = (struct cell*)x1;
    struct cell* c2 = (struct cell*)x2;
    
    //@ open [f1]cell(x1, v1);
    //@ open [f2]cell(x2, v2);
    
    bool result = (c1->val == c2->val);
    
    //@ close [f1]cell(x1, v1);
    //@ close [f2]cell(x2, v2);
    
    return result;
}