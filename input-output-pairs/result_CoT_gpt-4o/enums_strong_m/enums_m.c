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
