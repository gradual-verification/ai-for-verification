#include <assert.h>

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

/*@
  //inductive day = monday | tuesday | wednesday | thursday | friday | saturday | sunday;
  predicate valid_day(enum day d) = d == monday || d == tuesday || d == wednesday || d == thursday || d == friday || d == saturday || d == sunday;
  
  lemma void day_range(enum day d)
  requires valid_day(d);
  ensures 0 <= d && d <= 6;
  {
    open valid_day(d);
    switch(d) {
      case monday: case tuesday: case wednesday:
      case thursday: case friday: case saturday:
      case sunday:
    }
  }
  
  lemma void next_day_range(int d)
  requires 0 <= d && d <= 6;
  ensures 0 <= (d + 1) % 7 && (d + 1) % 7 <= 6;
  {
    if (d == 6) {
      div_rem_nonneg_unique(d + 1, 7, 1, 0);
      assert ((d + 1) % 7 == 0);
    } else {
      div_rem_nonneg_unique(d + 1, 7, 0, d + 1);
      assert ((d + 1) % 7 == d + 1);
    }
  }
@*/

enum large_numbers
{
  large_number = 30000,
  another_large_number,
  yaln = -0x7fff - 1
};


enum day next_day(enum day d)
//@ requires valid_day(d);
//@ ensures 0 <= result && result <= 6;
{
  /*@ day_range(d); @*/
  int next = (d + 1) % 7;
  /*@ next_day_range(d); @*/
  return next;
}

/* @
  lemma void valid_large_numbers()
  requires true;
  ensures large_number == 30000;
  ensures another_large_number == 30001;
  ensures yaln + 1 == -0x7fff;
  {
  }
@*/

int main()
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  /* @ valid_large_numbers(); @*/
  d = 35; /* Not safe, for demonstration only */
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
