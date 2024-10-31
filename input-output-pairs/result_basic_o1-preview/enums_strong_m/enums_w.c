enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires d == monday || d == tuesday || d == wednesday || d == thursday || d == friday || d == saturday || d == sunday;
//@ ensures result == (d == sunday ? monday : (enum day)(d + 1));
{
  if (d == sunday) {
    return monday;
  } else {
    return (enum day)(d + 1);
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
  //@ assert large_number == 30000;
  //@ assert another_large_number == 30001;
  //@ assert yaln + 1 == -0x7fff;
  return 0;
}
