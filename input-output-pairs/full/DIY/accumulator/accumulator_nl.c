#include "stdlib.h"

struct Accumulator {
  int total;
  int count; // keeps track of how many times add/subtract has been called
};

/***
 * Description:
 * The `create` function creates a new accumulator with the given value
 *
 * @param val: the given value
 *
 * The function allocates memory for a new `Accumulator`, sets its total as val and sets its count as 1. 
 * It makes sure that the created accumulator satsifies the property of Accumulator. 
 */
struct Accumulator* create(int v)
{
  struct Accumulator* a = malloc(sizeof(struct Accumulator));
  if (a == 0) {
    abort();
  }
  a->total = v;
  a->count = 1;
  return a;
}

/***
 * Description:
 * The `add` function adds up the value in the accumulator with a given value. 
 * 
 * @param a: the given accumulator, which has the property of Accumulator
 * @param x: the given value
 *
 * The function updates the total and count of the accumulator, and makes sure it has the property of Accumulator.
 */
void add(struct Accumulator* a, int x)
{
  a->total += x;
  a->count += 1;
}

/***
 * Description:
 * The `subtract` function subtracts the value in the accumulator by a given value. 
 * 
 * @param a: the given accumulator, which has the property of Accumulator
 * @param x: the given value
 *
 * The function updates the total and count of the accumulator, and makes sure it has the property of Accumulator.
 */
void subtract(struct Accumulator* a, int x)
{
  a->total -= x;
  a->count += 1;
}

/***
 * Description:
 * The `reset` function resets the accumulator. 
 * 
 * @param a: the given accumulator, which has the property of Accumulator
 *
 * The function resets the total and count of the accumulator to 0, and makes sure it has the property of Accumulator.
 */
void reset(struct Accumulator* a)
{
  a->total = 0;
  a->count = 0;
}

/***
 * Description:
 * The `current` function returns the total of a given accumulator. 
 * 
 * @param a: the given accumulator, which has the property of Accumulator
 *
 * The function makes sure the accumulator keeps the property of Accumulator.
 */
int current(struct Accumulator* a)
{
  int tmp = a->total;
  return tmp;
}

/***
 * Description:
 * The `average` function returns the average value of each operation (i.e., total/count). 
 * 
 * @param a: the given accumulator, which has the property of Accumulator and its count > 0
 *
 * The function makes sure the accumulator keeps the property of Accumulator.
 */
int average(struct Accumulator* a)
{
  int avg = a->total / a->count;
  return avg;
}

/***
 * Description:
 * The `destroy` function disposes a given accumulator.
 * 
 * @param a: the given accumulator, which has the property of Accumulator
 *
 * The function makes sure the accumulator is freed. 
 */
void destroy(struct Accumulator* a)
{
  free(a);
}

/***
 * Description:
 * The `main` function tests the operations of Accumulator. 
 */
int main() //@ : main
{
  struct Accumulator* acc = create(10);
  add(acc, 5);        // total = 15, count = 2
  subtract(acc, 3);   // total = 12, count = 3
  int avg = average(acc); 
  reset(acc);         // total = 0, count = 0
  add(acc, 8);        // total = 8, count = 1
  destroy(acc);
  return 0;
}