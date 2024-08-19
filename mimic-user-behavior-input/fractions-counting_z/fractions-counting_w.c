#include "stdlib.h"

struct C {
  int x;
};
//remove the malloc block
struct C* create_C(int x) 
  //@ requires true;
  //@ ensures result->x |-> x 
{
  struct C* c = malloc(sizeof(struct C));
  if (c == 0) {
    abort();
  } 
  c->x = x;
  return c;
}





int main() 
  //@ requires true;
  //@ ensures true;
{
  struct C* c = create_C(5);

  bool b = random();
  int n = 0;
  while (b) 
   
  {
    
    n = n + 1;
    b = random();
  }

  while (n > 0) 

  {
 
    n = n - 1;
  }

  free(c);
  return 0;
}

int main2()
//@ requires true;
//@ ensures true;
{
  struct C* c = create_C(3);
 
  free(c);
  return 0;
}
