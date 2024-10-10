Certainly! Below is the C code with a formal verification specification written for VeriFast.

```c
enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };
enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1 };

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures 0 <= result && result < 7;
{
  return (d + 1) % 7;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;
  //@ assert d == monday;
  // Assigning an invalid enum value, however, in C enums are not strict and don't cause an error by themselves
  d = 35; 
  int x = d;
  //@ assert x == 35;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
```

### Explanation:

- **Enum Definition**: The `enum day` and `enum large_numbers` are defined as before. VeriFast doesn't have specific requirements here, since enums can be used as integers in C.

- **Verified Function `next_day`**:
  - Receives an argument `d` with a precondition ensuring it is within valid bounds `[0, 7)`.
  - Ensures that the result also lies within valid bounds `[0, 7)`.
  - This function returns the next day, cyclically.

- **Verification Properties in `main()`**:
  - The `main()` function begins with no specific pre-conditions and must ensure post-conditions are met. Here, `true` is specified for simplicity.
  - Assignment operations and assertions check values at runtime, but not strictly required for VeriFast.
  - Assertions have been added to verify assumptions about current values, including C enum behavior which would typically raise a flag in static analysis for assigning a value outside an enum range.
  
The code above assumes the VeriFast tool is set up to understand these specifications and verifies the logic according to those proofs and assertions.
