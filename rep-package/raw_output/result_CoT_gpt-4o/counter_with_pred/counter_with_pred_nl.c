#include "stdlib.h"

// VeriFast predicates to represent the state of a Counter structure
predicate Counter(struct Counter* c; int v) =
  malloc_block_Counter(c) &*&
  c->value |-> v;

// Predicate for valid pointer to a Counter structure
predicate valid_counter_ptr(struct Counter* c) =
  c != 0;

// Function to initialize a new Counter with a specified value
struct Counter* init(int v)
  //@ requires true;
  //@ ensures Counter(result, v) &*& valid_counter_ptr(result);
{
  struct Counter* c = malloc(sizeof(struct Counter));
  if (c == 0) {
    abort();
  }
  c->value = v;
  //@ close Counter(c, v);
  //@ close valid_counter_ptr(c);
  return c;
}

// Function to increment the value of a Counter
void increment(struct Counter* c)
  //@ requires Counter(c, ?v) &*& valid_counter_ptr(c);
  //@ ensures Counter(c, v + 1) &*& valid_counter_ptr(c);
{
  //@ open Counter(c, v);
  int tmp = c->value;
  c->value = tmp + 1;
  //@ close Counter(c, tmp + 1);
}

// Function to deallocate the memory for a Counter
void dispose(struct Counter* c)
  //@ requires Counter(c, ?v) &*& valid_counter_ptr(c);
  //@ ensures true;
{
  //@ open Counter(c, v);
  //@ open valid_counter_ptr(c);
  free(c);
}

// Function to swap values between two Counters
void swap(struct Counter* c1, struct Counter* c2)
  //@ requires Counter(c1, ?v1) &*& Counter(c2, ?v2) &*& valid_counter_ptr(c1) &*& valid_counter_ptr(c2);
  //@ ensures Counter(c1, v2) &*& Counter(c2, v1) &*& valid_counter_ptr(c1) &*& valid_counter_ptr(c2);
{
  //@ open Counter(c1, v1);
  //@ open Counter(c2, v2);
  int tmp1 = c1->value;
  int tmp2 = c2->value;
  c2->value = tmp1;
  c1->value = tmp2;
  //@ close Counter(c1, v2);
  //@ close Counter(c2, v1);
}

// Function to get the current value of a Counter
int get(struct Counter* c)
  //@ requires Counter(c, ?v) &*& valid_counter_ptr(c);
  //@ ensures Counter(c, v) &*& valid_counter_ptr(c) &*& result == v;
{
  //@ open Counter(c, v);
  int tmp = c->value;
  //@ close Counter(c, v);
  return tmp;
}

// The main function to demonstrate the use of Counter structures
int main()
  //@ : main
  //@ requires true;
  //@ ensures true;
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
