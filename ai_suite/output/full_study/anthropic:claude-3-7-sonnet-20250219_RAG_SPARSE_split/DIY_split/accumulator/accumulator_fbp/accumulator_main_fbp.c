#include "stdlib.h"

struct Accumulator {
  int total;
  int count;
};

/*@
predicate Accumulator(struct Accumulator* a, int t, int c) =
  a->total |-> t &*& a->count |-> c &*& malloc_block_Accumulator(a);
@*/

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

void add(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& INT_MIN <= t + x &*& t <= INT_MAX - x &*& c < INT_MAX;
  //@ ensures Accumulator(a, t + x, c + 1);
{
  a->total += x;
  a->count += 1;
}

void add_multiple(struct Accumulator* a, int n, int x)
/*@
  requires Accumulator(a, ?t, ?c) 
           &*& n >= 1 &*& x >= 0
           &*& t + n * x <= INT_MAX
           &*& c + n <= INT_MAX;
@*/
/*@
  ensures Accumulator(a, t + n * x, c + n);
@*/
{
  //@ open Accumulator(a, t, c);
  int i = 0;
  while (i < n)
  //@ invariant a->total |-> t + i * x &*& a->count |-> c + i &*& malloc_block_Accumulator(a) &*& 0 <= i &*& i <= n;
  {
    a->total += x;
    a->count += 1;
    i++;
  }
  //@ close Accumulator(a, t + n * x, c + n);
}

void subtract(struct Accumulator* a, int x)
  //@ requires Accumulator(a, ?t, ?c) &*& t - x <= INT_MAX &*& t - x >= INT_MIN &*& c < INT_MAX;
  //@ ensures Accumulator(a, t - x, c + 1);
{
  a->total -= x;
  a->count += 1;
}

void reset(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures Accumulator(a, 0, 0);
{
  //@ open Accumulator(a, _, _);
  a->total = 0;
  a->count = 0;
  //@ close Accumulator(a, 0, 0);
}

int average(struct Accumulator* a)
  //@ requires Accumulator(a, ?t, ?c) &*& c > 0;
  //@ ensures Accumulator(a, t, c) &*& result == t / c;
{
  //@ open Accumulator(a, t, c);
  int avg = a->total / a->count;
  //@ close Accumulator(a, t, c);
  return avg;
}

void destroy(struct Accumulator* a)
  //@ requires Accumulator(a, _, _);
  //@ ensures true;
{
  //@ open Accumulator(a, _, _);
  free(a);
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct Accumulator* acc = create(10);
  
  //@ assert Accumulator(acc, 10, 1);
  
  // Check preconditions for add
  //@ assert INT_MIN <= 10 + 5;
  //@ assert 10 <= INT_MAX - 5;
  //@ assert 1 < INT_MAX;
  add(acc, 5);
  
  //@ assert Accumulator(acc, 15, 2);
  
  // Check preconditions for subtract
  //@ assert 15 - 3 <= INT_MAX;
  //@ assert 15 - 3 >= INT_MIN;
  //@ assert 2 < INT_MAX;
  subtract(acc, 3);
  
  //@ assert Accumulator(acc, 12, 3);
  
  // Check preconditions for average
  //@ assert 3 > 0;
  int avg = average(acc);
  
  //@ assert avg == 12 / 3;
  
  reset(acc);
  
  //@ assert Accumulator(acc, 0, 0);
  
  // Check preconditions for add_multiple
  //@ assert 2 >= 1;
  //@ assert 8 >= 0;
  //@ assert 0 + 2 * 8 <= INT_MAX;
  //@ assert 0 + 2 <= INT_MAX;
  add_multiple(acc, 2, 8);
  
  //@ assert Accumulator(acc, 16, 2);
  
  destroy(acc);
  
  return 0;
}