#include "verifast.h"

enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures d == 6 ? result == 0 : result == d + 1;
{
  if (d == 6) {
  } else {
  }
  return (d + 1) % 7;
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  d = 35; 

  switch (d) {
    case 0 : break;
    case 1 : break;
    case 2 : break;
    case 3 : break;
    case 4 : break;
    case 5 : break;
    case 6 : break;
    default : break;
  }

  int x = d;
  
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);

  return 0;
}
