typedef int my_int;

int main()
//@ requires true;
//@ ensures true;
{
    my_int x = 5;
    int y = x;
    my_int z = 3;
    my_int t = x + z;
    assert(t == 8); // This checks if the calculated value matches the expected result
    return 0;
}
