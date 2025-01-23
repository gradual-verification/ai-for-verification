enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures d == 6 ? result == 0 : result == d + 1;
{
  if (d == 6) {
    //@ assert d == 6;
    return 0;
  } else {
    //@ assert 0 <= d && d < 6;
    return d + 1;
  }
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
  enum day d = monday;
  //@ assert monday == 0;
  d = (enum day)35; // Explicit cast to suppress warnings about invalid enum assignment
  int x = d;
  //@ assert x == 35;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
