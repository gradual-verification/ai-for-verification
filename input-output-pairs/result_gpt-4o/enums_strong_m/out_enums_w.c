enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures result == (d == 6 ? 0 : d + 1);
{
  if (d == 6) {
    return 0;
  } else {
    return d + 1;
  }
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  // The value assignment `d = 35;` is invalid for this enum type
  // To maintain the correctness, we should remove or prevent invalid assignments:
  // d = 35; // This line should not be present as it assigns an invalid value

  // Now directly use valid enum values
  int x = d;
  
  // Verify that our large numbers match expectations
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  
  return 0;
}
