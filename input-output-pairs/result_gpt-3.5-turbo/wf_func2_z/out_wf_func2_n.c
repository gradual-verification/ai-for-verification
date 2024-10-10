//@ #include <stdint.h>

// Specification for the fill function
//@ predicate fill_chars(char *buf, int length, char c) = length == 0 ? true : buf[length-1] == c &*& fill_chars(buf, length - 1, c);

void fill(char *buf, int length, char c)
    //@ requires buf[0..length] |-> _ &*& 0 <= length;
    //@ ensures  fill_chars(buf, length, c);
{
    for (int i = 0; i < length; i++)
    //@ requires buf[i..length] |-> _ &*& 0 <= i &*& i <= length;
    //@ ensures  fill_chars(buf, length, c);
    {
        buf[i] = c;
    }
}

int main()
{
    //@ int length = 5;
    //@ char buf[length];
    //@ fill(buf, length, 'X');
    return 0;
}
