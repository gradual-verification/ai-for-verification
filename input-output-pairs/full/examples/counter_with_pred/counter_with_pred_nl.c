#include "stdlib.h"

struct Counter {
  int value;
};

/* init() function
-parameter: an integer
-description: creates a Counter with the 
given value*/
struct Counter* init(int v)
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;

  return c;
}

/* increment() function
-parameter: a pointer to a Counter
-description: increments the value of 
the Counter by 1*/
void increment(struct Counter* c)
{
  int tmp = c->value;
  c->value = tmp + 1;
}

/* dispose() function
-parameter: a pointer to a Counter
-description: frees the memory allocated for the Counter*/
void dispose(struct Counter* c)
{
  free(c);
}

/* swap() function
-parameter: two pointers to Counters
-description: swaps the values of the two Counters*/
void swap(struct Counter* c1, struct Counter* c2)
{
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
}

/* get() function
-parameter: a pointer to a Counter
-description: returns the value of the Counter*/
int get(struct Counter* c)
{
  int tmp = c->value;
  return tmp;
}

/*main() function
-parameter: none
-description: creates two counters, increments 
the first one, swaps the values of the two 
counters, and returns the value of the second 
counter*/
int main() //@ : main
{
  struct Counter* c1 = init(0); struct Counter* c2 = init(5);

  increment(c1); swap(c1, c2); int tmp = get(c2);

  dispose(c1); dispose(c2);
  return 0;
}
