```c
#include <stdbool.h>

enum day {
  monday,
  tuesday,
  wednesday,
  thursday,
  friday,
  saturday,
  sunday
};

enum large_numbers {
  large_number = 30000,
  another_large_number,
  yaln = -0x7fff - 1
};

// Predicate to specify valid enum day
/*@
predicate valid_day(enum day d) = 
  d >= monday && d <= sunday;
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
@*/
enum day next_day(enum day d) 
{
  if (d == 6) {
    // handle edge case when d is sunday
  } else {
    // handle other days
  }
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
  enum day d = monday;

  // Assigning 35 is outside the valid range [0, 6] for enum day
  // In a real-world critical system, this should raise an error
  d = (enum day) 35;
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
```

### Explanation:

1. **Predicate Definition:**
   - A predicate `valid_day` is defined to assert that a given day is valid within the enum day range.
  
2. **Function precondition and postcondition:**
   - `next_day` function has a precondition to ensure the input `d` is within the valid range.
   - The postcondition ensures the result is also a valid day within the enum range.
  
3. **Casting Warning:**
   - In `main`, `d` is cast to `35`, which is outside the valid range for `enum day`. This is flagged in comments for critical systems to address.

4. **Assertions on Enums:**
   - Verified the expected values of `large_number`, `another_large_number`, and `yaln` to ensure correctness.

This code specification ensures the `next_day` function handles its operations correctly and safely within the defined enum range.
