```c
typedef int my_int;

int main()
//@ requires true;
//@ ensures true;
{
    my_int x = 5;
    //@ assert x == 5;

    int y = x;
    //@ assert y == x;

    my_int z = 3;
    //@ assert z == 3;

    my_int t = x + z;
    //@ assert t == x + z;
    //@ assert t == 5 + 3;
    //@ assert t == 8;

    assert(t == 8);
    return 0;
}
```
