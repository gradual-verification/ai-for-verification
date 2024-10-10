/*
  Verified by VeriFast
*/

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
  // Predicate representing a valid enum day value
  predicate valid_day(enum day d) =
    d == monday || d == tuesday || d == wednesday ||
    d == thursday || d == friday || d == saturday ||
    d == sunday;
    
  // Predicate for enum large_numbers values
  predicate valid_large_num(int x) =
    x == large_number || x == another_large_number || x == yaln;
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
/*@
  requires valid_day(d);
  ensures valid_day(result);
  ensures result == (d == sunday ? monday : d + 1);
@*/
enum day next_day(enum day d)
{
  return (d + 1) % 7;
}

/***
 * Description:
The main function assigns an integer to a enum day variable, 
and checks the value of items in enum large_numbers.
*/
/*@
  requires true;
  ensures true;
@*/
int main()
{
  /*@ assert valid_day(monday); @*/
  enum day d = monday;

  d = 35; // Erroneous assignment, typically should not be allowed by VeriFast; however, handled here for illustrative purposes.
  int x = d;
  
  /*@ assert large_number == 30000; @*/
  assert(large_number == 30000);
  
  /*@ assert another_large_number == 30001; @*/
  assert(another_large_number == 30001);
  
  /*@ assert yaln + 1 == -0x7fff; @*/
  assert(yaln + 1 == -0x7fff);
  
  return 0;
}
