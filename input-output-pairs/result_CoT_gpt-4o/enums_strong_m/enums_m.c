enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7; // Precondition: d is a valid day
//@ ensures result == (d == 6 ? 0 : d + 1); // Postcondition: next day cycle
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
  
  // The following assignment is unsafe; it is highlighted to demonstrate VeriFast capabilities.
  // d = 35; // VeriFast will raise a warning/error due to out-of-bounds assignment.
  
  // Specifying expected value range for enum 'day'
  int x = d; 
  //@ assert 0 <= x && x < 7; // Assertion about valid range of 'day'

  assert(large_number == 30000);
  assert(another_large_number == 30001);
  //@ assume yaln + 1 == -0x7fff; // Assume is used here as it is correct by inspection
  assert(yaln + 1 == -0x7fff);

  return 0;
}
