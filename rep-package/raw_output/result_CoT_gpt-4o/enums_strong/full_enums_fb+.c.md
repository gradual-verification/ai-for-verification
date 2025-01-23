```c
enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1 };

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures (d == sunday ? result == monday : result == d + 1) && 0 <= result && result < 7;
{
  if (d == sunday) {
    //@ assert d == sunday;
    return monday;
  } else {
    //@ assert d < sunday;
    return d + 1;
  }
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  //@ assert d == monday;
  d = next_day(d);
  //@ assert d == tuesday;
  
  int x = d;
  //@ assert x == tuesday;
  
  //@ assert large_number == 30000;
  //@ assert another_large_number == 30001;
  //@ assert yaln + 1 == -0x7fff;
  
  return 0;
}
```

In this code:

- Precondition and postcondition are added to the `next_day` function to ensure the input is a valid day of the week and the output is the next day, cycling back to monday after sunday.
- Assertions are used within the `next_day` function to ensure the correctness of logical branches.
- In `main`, additional assertions help trace how values are manipulated and ensure that result assumptions made are correct.
- Enum values are validated using assertions to confirm they hold the correct values.
