```c CODE and SPEC
#include "stdlib.h"

struct Counter {
  int value;
};

/*@ 
predicate counter(struct Counter* c; int v) = c != NULL &*& c->value |-> v;

@*/

/*@ 
requires true;
ensures true;
assigns \nothing;
*/
struct Counter* init(int v)
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close counter(c, v);
  return c;
}

/*@ 
requires counter(c, ?v) &*& v < INT_MAX;
ensures counter(c, v + 1);
assigns c->value;
*/
void increment(struct Counter* c)
{
  c->value++;
}

/*@ 
requires counter(c, _);
ensures true;
assigns \nothing;
*/
void dispose(struct Counter* c)
{
  free(c);
  //@ open counter(c, _);
}

/*@ 
requires counter(c, ?v) &*& counter(d, ?w);
ensures counter(c, w) &*& counter(d, v);
assigns c->value, d->value;
*/
void swap(struct Counter* c, struct Counter* d)
{
  int tmp = c->value;
  c->value = d->value;
  d->value = tmp;
}

/*@ 
requires counter(c, ?v);
ensures counter(c, v) &*& result == v;
assigns \nothing;
*/
int get(struct Counter* c)
{
  //@ open counter(c, _);
  return c->value;
}

/*@ 
requires true;
ensures true;
assigns \nothing;
*/
int main() //@ : main
{
  struct Counter* c1 = init(0); 
  struct Counter* c2 = init(5);

  increment(c1); 
  swap(c1, c2); 
  int tmp = get(c2);

  dispose(c1); 
  dispose(c2);

  return 0;
}
```
