enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires 0 <= d && d < 7;
//@ ensures d == 6 ? result == 0 : result == d + 1;
{
  if (d == 6) {
    //@ div_rem_nonneg_unique(d + 1, 7, 1, 0);
  } else {
    //@ div_rem_nonneg_unique(d + 1, 7, 0, d + 1);
  }
  return (d + 1) % 7;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  enum day d = monday;
  //@ assert d == 0;
  //@ assert sunday == 6;
  d = 35;
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
