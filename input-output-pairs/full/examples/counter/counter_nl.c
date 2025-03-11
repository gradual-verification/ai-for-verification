#include "stdlib.h"

struct Counter {
  int value;
};

/*init() function
-params: an integer
-description: creates a new counter with the given value*/
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
-params: a Counter pointer
-description: increments the value of the counter by 1*/
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}

/*dispose() function
-params: a Counter pointer
-description: frees the memory allocated for the counter*/
void dispose(struct Counter* c)
{
  free(c);
}

/*swap() function
-params: two Counter pointers
-description: swaps the values of the two counters*/
void swap(struct Counter* c1, struct Counter* c2)
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

/*main() function
-params: none
-description: creates two counters, increments the 
first one, swaps the values of the two counters, 
and disposes of them*/
int main() //@ : main
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = c2->value;
  dispose(c1); dispose(c2);
  return 0;
}
