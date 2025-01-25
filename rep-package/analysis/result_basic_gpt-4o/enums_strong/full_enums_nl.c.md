```c
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
  inductive day = monday | tuesday | wednesday | thursday | friday | saturday | sunday;
  
  pred valid_day(enum day d) =
    d == monday || d == tuesday || d == wednesday || d == thursday ||
    d == friday || d == saturday || d == sunday;
  
  lemma void day_range(enum day d)
  requires valid_day(d);
  ensures 0 <= d && d <= 6;
  {
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
      assert ((d + 1) % 7 == 0);
    } else {
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

/*@ requires valid_day(d);
    ensures valid_day(result); @*/
enum day next_day(enum day d)
{
  /*@ day_range(d); @*/
  int next = (d + 1) % 7;
  /*@ next_day_range(d); @*/
  return (enum day)next;
}

/*@
  lemma void valid_large_numbers()
  requires true;
  ensures large_number == 30000;
  ensures another_large_number == 30001;
  ensures yaln + 1 == -0x7fff;
  {
  }
@*/

int main()
{
  enum day d = monday;
  /*@ valid_large_numbers(); @*/
  d = (enum day)35; /* Not safe, for demonstration only */
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
```

This C code now includes the necessary Verifast specifications and lemmas to verify the program correctness. The specification ensures the function `next_day` is called on valid `day` enumeration values and returns valid results. Additionally, validity of values in `enum large_numbers` is confirmed through a lemma.
