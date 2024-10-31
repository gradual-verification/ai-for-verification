/*@
fixpoint list<char> repeat_char(char c, int n) {
    return n <= 0 ? nil : cons(c, repeat_char(c, n - 1));
}
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, _);
//@ ensures chars(buf, length, repeat_char(c, length));
{
    int i = 0;
    while (i < length)
    /*@
    invariant
        0 <= i &*& i <= length &*&
        chars(buf, i, repeat_char(c, i)) &*&
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

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
