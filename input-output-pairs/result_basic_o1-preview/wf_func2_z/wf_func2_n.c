#include "arrays.gh"

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, _);
//@ ensures chars(buf, length, repeat(c, length));
{
    int i = 0;
    while (i < length)
    /*@
    invariant
        0 <= i &*& i <= length &*&
        chars(buf, i, repeat(c, i)) &*&
        chars(buf + i, length - i, _);
    @*/
    {
        //@ chars_split(buf + i, 1);
        //@ open chars(buf + i, 1, _);
        buf[i] = c;
        //@ close chars(buf + i, 1, cons(c, nil));
        //@ chars_join(buf + i);
        i++;
    }
    //@ chars_join(buf);
}
