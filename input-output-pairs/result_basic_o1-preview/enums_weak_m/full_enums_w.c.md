```c
enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
  //@ requires true;
  //@ ensures 0 <= result && result < 7;
{
  int res = (d + 1) % 7;
  if (res < 0)
    //@ assert res < 0;
    res += 7;
  //@ assert 0 <= res && res < 7;
  return res;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  //@ assert monday == 0;
  //@ assert tuesday == 1;
  //@ assert wednesday == 2;
  //@ assert thursday == 3;
  //@ assert friday == 4;
  //@ assert saturday == 5;
  //@ assert sunday == 6;
  
  enum day d = monday;
  d = (enum day)35;
  int x = d;
  //@ assert d == 35;
  //@ assert x == 35;
  //@ assert large_number == 30000;
  //@ assert another_large_number == 30001;
  //@ assert yaln + 1 == -0x7fff;
  return 0;
}
```
