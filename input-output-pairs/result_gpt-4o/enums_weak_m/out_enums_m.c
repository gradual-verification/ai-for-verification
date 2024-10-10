#include <stdbool.h>

enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

enum day next_day(enum day d)
//@ requires day(d);
//@ ensures day(result);
{
    return (d + 1) % 7;
}

bool day(enum day d) 
//@ requires true;
//@ ensures result == (0 <= d && d < 7);
{
    return 0 <= d && d < 7;
}

int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
    enum day d = monday;
    //@ assert day(d);
    
    d = next_day(d);
    //@ assert day(d);

    int x = d;
    //@ assert large_number == 30000;
    //@ assert another_large_number == 30001;
    //@ assert yaln + 1 == -0x7fff;

    return 0;
}
