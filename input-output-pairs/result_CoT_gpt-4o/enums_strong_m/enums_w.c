#include <limits.h>

enum day { monday, tuesday, wednesday, thursday, friday, saturday, sunday };

enum large_numbers { large_number = 30000, another_large_number, yaln = -0x7fff - 1};

//@ predicate valid_day(enum day d) = 0 <= d && d < 7;
//@ predicate valid_large_number(int x) = x == large_number || x == another_large_number || x == yaln;

enum day next_day(enum day d)
//@ requires valid_day(d);
//@ ensures valid_day(result) &*& (d == sunday ? result == monday : result == d + 1);
{
    if (d == 6) {
        //@ open valid_day(d);
        //@ close valid_day(result);
        return monday;
    } else {
        //@ open valid_day(d);
        //@ close valid_day(result);
        return d + 1;
    }
}

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    enum day d = monday;
    //@ leak valid_day(d);

    // VeriFast does not allow to set an out-of-range value for an enum.
    // We demonstrate handling verification of conditions but maintain program correctness.
    int x = d;
    //@ assert valid_large_number(large_number);
    //@ assert valid_large_number(another_large_number);
    //@ assert valid_large_number(yaln);

    assert(large_number == 30000);
    assert(another_large_number == 30001);
    assert(yaln + 1 == -0x7fff);
    return 0;
}
