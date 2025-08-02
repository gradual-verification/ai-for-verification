#include "stdlib.h"
#include "assert.h"
#include <stdbool.h>
#include "malloc.h"

//@ #include "arrays.gh"
//@ #include "list.gh"

// TODO: make this function pass the verification
void array_test2(int* a)
  //@ requires a[..?n] |-> ?vs &*& 1 < n;
  //@ ensures a[..n] |-> update(0, 10, vs);
{
  int a1_old = a[1];
  //@ open ints_(a, n, vs);
  a[0] = 10;
  //@ close ints_(a, n, update(0, 10, vs));
  int tmp = a[0];
  assert(tmp == 10);
  int a1 = a[1];
  assert(a1_old == a1);
}