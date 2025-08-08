p->name |-> _ &*& p->spouse |-> 0
p->name |-> _ &*& p != s &*& [1/2]p->spouse |-> s &*& [1/2]s->spouse |-> p

struct person {
  char* name;
  struct person* spouse;
};



void marry(struct person *this, struct person *other)
{
  this->spouse = other;
  other->spouse = this;
}
