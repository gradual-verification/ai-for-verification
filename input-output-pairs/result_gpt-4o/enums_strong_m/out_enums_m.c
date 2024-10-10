enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures d == sunday ? result == monday : result == d + 1;
{
  if (d == sunday) {
    return monday;
  } else {
    return d + 1;
  }
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  // Remove or change the following line, as it assigns an invalid value to an enum variable.
  // d = 35; // Invalid assignment to an enum type.
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
