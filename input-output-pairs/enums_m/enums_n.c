enum day
{
  monday,
  tuesday,
  wednesday,
  thursday,
  friday,
  saturday,
  sunday
};

enum large_numbers
{
  large_number = 30000,
  another_large_number,
  yaln = -0x7fff - 1
};

/***
 * Description:
This function calculates the next day given a current day.

@param day d - represents the current day.

The function calculates the next day by adding 1 to 
the current day, taking the result modulo 7 to handle looping 
back to Monday after Sunday. Finally, the function returns 
the next day as an enum day type, ensuring that the result is 
within the valid range of 0 to 6.
*/
enum day next_day(enum day d)
{

  return (d + 1) % 7;
}

int main()
{
  enum day d = monday;

  d = 35;
  int x = d;
  assert(large_number == 30000);
  assert(another_large_number == 30001);
  assert(yaln + 1 == -0x7fff);
  return 0;
}
