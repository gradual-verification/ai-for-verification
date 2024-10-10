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
predicate valid_day(enum day d) = d >= monday && d <= sunday;
predicate valid_large_numbers() = large_number == 30000 &*& another_large_number == 30001 &*& yaln == -0x7fff - 1;
predicate next_day_post(enum day d, enum day result) = d == sunday ? result == monday : result == (enum day)((int)d + 1) % 7;
predicate next_day_pre(enum day d) = valid_day(d);

@*/

/***
 * Description:
The next_day function calculates the next day given a current day.

@param day d - represents the current day, which is in the range of [0, 6].

The function calculates the next day by adding 1 to 
the current day, taking the result modulo 7 to handle looping 
back to Monday after Sunday. Finally, the function returns 
the next day as an enum day type, ensuring that the result is 
within the valid range of 0 to 6.
*/
enum day next_day(enum day d)
  /*@
  requires
    next_day_pre(d);
  ensures
    next_day_post(d, result);
  @*/
{
  //@open next_day_pre(d);

  enum day result;
  if (d == sunday) {
    result = monday;
  } else {
    result = (enum day)((int)d + 1) % 7;
  }

  //@close next_day_post(d, result);
  return result;
}

/***
 * Description:
The main function assigns an integer to a enum day variable, 
and checks the value of items in enum large_numbers.
*/
int main()
  /*@
  requires true;
  ensures
    valid_day(monday) &*& valid_large_numbers() &*&
    next_day_post(monday, (enum day)((int)monday + 1) % 7);
  @*/
{
  enum day d = monday;

  d = 35; // This will be flagged as incorrect during verification
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
```
