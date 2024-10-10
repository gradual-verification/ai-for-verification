#include "stdlib.h"

struct person {
  char* name;
  struct person* spouse;
};

//@malloc_tag: Expects_memory_leak
//@post: The returned person struct has spouse set to null
//@allocates(Expects_memory_leak)
struct person *create_person()
{
  struct person *p = malloc(sizeof(struct person));
  if(p == 0) abort();
  p->spouse = 0;
  return p;
}

//@require !this->spouse && !other->spouse
//@post: this->spouse == other && other->spouse == this
void marry(struct person *this, struct person *other)
{
  this->spouse = other;
  other->spouse = this;
}

//@require this != null
//@returns: this->spouse
struct person* person_get_spouse(struct person* this)
{
  return this->spouse;
}

//@require this != null && this->spouse != null
//@post: this->spouse == null && spouse->spouse == null
void divorce(struct person* this)
{
  this->spouse->spouse = 0;
  this->spouse = 0;
}

//@require this != null
//@post: If spouse exists, spouse->spouse == null (memory clean) and this is freed
void die(struct person *this)
{
  if(this->spouse != 0) {
    this->spouse->spouse = 0;
  }
  free(this); 
}

//@post: Memory is correctly allocated, utilized, and freed in the sequence of steps
int main() //@ : main
{
  struct person* alice = create_person();
  struct person* bob = create_person();
  struct person* eve = 0;
  marry(alice, bob);
  eve = create_person();
  divorce(bob);
  marry(bob, eve);
  die(alice);
  die(bob);
  die(eve);
  return 0;
}
