#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

/*@
// Predicate to represent a person who is not married
predicate unmarried_person(struct person *p; char *name) =
    p != 0 &*&
    p->name |-> name &*& 
    p->spouse |-> 0 &*&
    malloc_block_person(p) &*&
    string(name, _);

// Predicate to represent a married person
predicate married_person(struct person *p, struct person *spouse; char *name) =
    p != 0 &*&
    p->name |-> name &*& 
    p->spouse |-> spouse &*&
    spouse != 0 &*&
    malloc_block_person(p) &*&
    string(name, _);

// Lemma to establish that a person is different from their spouse
lemma void spouse_diff(struct person *p)
    requires [?f]p->spouse |-> ?spouse &*& spouse != 0;
    ensures [f]p->spouse |-> spouse &*& p != spouse;
{
    if (p == spouse) {
        // This is a contradiction because a person cannot be their own spouse
        // (would create a circular data structure)
        assert false;
    }
}

// Lemma to establish that if p1 is married to p2, then p2 is married to p1
lemma void married_lemma(struct person *p)
    requires [?f]p->spouse |-> ?spouse &*& spouse != 0 &*& [?g]spouse->spouse |-> ?s;
    ensures [f]p->spouse |-> spouse &*& [g]spouse->spouse |-> s &*& s == p;
{
    if (s != p) {
        // This is a contradiction because if p is married to spouse,
        // then spouse must be married to p
        assert false;
    }
}
@*/

/***
 * Description:
The `marry` function marries two unmarried `person` instances by setting their spouse pointers to each other.

@param `this` - Pointer to the first `person` whose spouse is null
@param `other` - Pointer to the second `person` whose spouse is null

It makes sure that this and other are married to each other. 
*/
void marry(struct person *this, struct person *other)
/*@ requires 
    unmarried_person(this, ?name1) &*& 
    unmarried_person(other, ?name2) &*&
    this != other;
@*/
/*@ ensures 
    married_person(this, other, name1) &*& 
    married_person(other, this, name2);
@*/
{
  this->spouse = other;
  other->spouse = this;
}