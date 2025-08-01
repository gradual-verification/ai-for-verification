#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c;
@*/

// TODO: make this function pass the verification
struct Accumulator* create(int v)
  //@ requires true;
  //@ ensures Accumulator(result, v, 1);
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) {
    abort();
  }
  a->total = v;
  a->count = 1;
  return a;
}

// TODO: make this function pass the verification
void add(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures Accumulator(a, t + x, c + 1);
{
  a->total += x;
  a->count += 1;
}

// TODO: make this function pass the verification
void add_multiple(struct Accumulator* a, int n, int x)
/*@
  requires Accumulator(a, ?t, ?c) 
           &*& n >= 1 &*& x >= 0;
@*/
/*@
  ensures Accumulator(a, t + n * x, c + n);
@*/
{
  int i = 0;
  while (i < n)
  {
    a->total += x;
    a->count += 1;
    i++;
  }
}

// TODO: make this function pass the verification
void subtract(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures Accumulator(a, t - x, c + 1);
{
  a->total -= x;
  a->count += 1;
}

// TODO: make this function pass the verification
void reset(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures Accumulator(a, 0, 0);
{
  a->total = 0;
  a->count = 0;
}

// TODO: make this function pass the verification
int current(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c);
  //@ ensures Accumulator(a, t, c) &*& result == t;
{
  int tmp = a->total;
  return tmp;
}

// TODO: make this function pass the verification
int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c) &*& c > 0;
  //@ ensures Accumulator(a, t, c) &*& result == t / c;
{
  int avg = a->total / a->count;
  return avg;
}

// TODO: make this function pass the verification
void destroy(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures true;
{
  free(a);
}

// TODO: make this function pass the verification
int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct Accumulator* acc = create(10);
  add(acc, 5);
  subtract(acc, 3);
  int avg = average(acc); 
  reset(acc);
  add_multiple(acc, 2, 8);
  destroy(acc);
  return 0;
}