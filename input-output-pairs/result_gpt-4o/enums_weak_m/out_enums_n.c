#include <assert.h>

/*@
  // Invariant for the enum day type
  predicate valid_day(enum day d) =
    d == monday || d == tuesday || d == wednesday ||
    d == thursday || d == friday || d == saturday ||
    d == sunday;

  // Function specification
  requires valid_day(d);
  ensures valid_day(result);
  ensures result == ((d + 1) % 7);
@*/

enum day next_day(enum day d)
{
  return (enum day)((d + 1) % 7);
}

int main()
{
  enum day d = monday;

  /*@ 
    // Assume statement is used here just for demonstration; ideally, we shouldn't assign invalid values in the first place.
    assume valid_day(d);
  @*/
  
  // Ensure d is a valid enum day
  d = (enum day)35; // This would violate the valid_day invariant, generally not advised.
  assert(valid_day(d)); // This assertion would typically fail unless physically forced valid earlier with assume.

  int x = d;
  
  //@ assert large_number == 30000;
  //@ assert another_large_number == 30001;
  //@ assert yaln + 1 == -0x7fff;
  
  return 0;
}
