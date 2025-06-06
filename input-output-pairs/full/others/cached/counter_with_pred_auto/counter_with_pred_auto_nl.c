#include "stdlib.h"

struct Counter {
  int value;
};

/*init() function
-params: int v
-description: initializes a Counter struct with the given value
*/
struct Counter* init(int v)
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  return c;
}

/*increment() function
-params: struct Counter* c
-description: increments the value of the Counter struct by 1
*/
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}

/*dispose() function
-params: struct Counter* c
-description: frees the memory allocated for the Counter struct
*/
void dispose(struct Counter* c)
{
  free(c);
}

/*swap() function
-params: struct Counter* c1, struct Counter* c2
-description: swaps the values of the two Counter structs
*/
void swap(struct Counter* c1, struct Counter* c2)
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

/*get() function
-params: struct Counter* c
-description: returns the value of the Counter struct
*/
int get(struct Counter* c)
{
  return c->value;
}

/*main() function
-params: void
-description: main function to test the Counter struct
*/
int main() //@ : main
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = get(c2);
  assert(tmp == 1);
  
  dispose(c1); dispose(c2);
  return 0;
}
