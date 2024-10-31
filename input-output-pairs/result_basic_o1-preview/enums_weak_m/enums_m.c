#include "verifast.h"

enum day {
    monday = 0,
    tuesday = 1,
    wednesday = 2,
    thursday = 3,
    friday = 4,
    saturday = 5,
    sunday = 6
};

enum large_numbers {
    large_number = 30000,
    another_large_number,
    yaln = -0x7fff - 1
};

enum day next_day(enum day d)
  //@ requires true;
  //@ ensures 0 <= result &*& result <= 6;
{
  int res = (d + 1) % 7;
  if (res < 0)
    res += 7;
  //@ assert res >= 0 && res <= 6;
  return (enum day)res;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;
  d = (enum day)35;
  int x = d;
  enum day next = next_day(d);
  //@ assert 0 <= next && next <= 6;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -32767);
  return 0;
}
