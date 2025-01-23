typedef int my_int;

int main()
//@ requires true;
//@ ensures true;
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    //@ assert t == x + z;  // The sum is indeed x + z
    //@ assert t == 5 + 3;  // Substitute known values
    //@ assert t == 8;      // Simplifies to 8
    assert(t == 8);
    return 0;
}
