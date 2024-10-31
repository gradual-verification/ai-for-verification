enum day
{
  MONDAY = 0,
  TUESDAY = 1,
  WEDNESDAY = 2,
  THURSDAY = 3,
  FRIDAY = 4,
  SATURDAY = 5,
  SUNDAY = 6
};

enum large_numbers
{
  LARGE_NUMBER = 30000,
  ANOTHER_LARGE_NUMBER = 30001,
  YALN = -0x7fff - 1
};

/*@
  requires 0 <= d <= 6;
  ensures 0 <= result <= 6;
@*/
enum day next_day(enum day d)
{
  return (d + 1) % 7;
}

int main()
{
  enum day d = MONDAY;
  d = 35;
  int x = d;
  //@ assert LARGE_NUMBER == 30000;
  //@ assert ANOTHER_LARGE_NUMBER == 30001;
  //@ assert YALN + 1 == -0x7fff;
  return 0;
}
