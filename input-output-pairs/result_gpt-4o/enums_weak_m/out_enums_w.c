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
