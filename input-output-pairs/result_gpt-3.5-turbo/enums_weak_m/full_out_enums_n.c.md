```c CODE and SPEC 
#include <verifast.h>

enum day
{
  monday,
  tuesday,
  wednesday,
  thursday,
  friday,
  saturday,
  sunday
};

enum large_numbers
{
  large_number = 30000,
  another_large_number,
  yaln = -0x7fff - 1
};

/*@ 
predicate wraparound(int x) =
  x >= 0 &*& x < 7;

predicate next_day_spec(enum day d, enum day r) = 
  d == monday ? (r == tuesday) : 
  d == tuesday ? (r == wednesday) : 
  d == wednesday ? (r == thursday) : 
  d == thursday ? (r == friday) : 
  d == friday ? (r == saturday) : 
  d == saturday ? (r == sunday) : 
  d == sunday ? (r == monday) : 
  true;

predicate main_spec() = true;

@*/

enum day next_day(enum day d)
  //@ requires true;
  //@ ensures next_day_spec(d, result);
{
  return (d + 1) % 7;
}

int main()
  //@ requires true;
  //@ ensures main_spec();
{
  enum day d = monday;
  d = 35; // Intentionally assigning an invalid value to show verification error
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
```
