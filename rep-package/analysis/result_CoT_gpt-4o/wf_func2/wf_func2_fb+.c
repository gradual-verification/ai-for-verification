/*@
fixpoint_auto list<char> n_times(char x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _ &*& 0 <= length &*& chars(buf, length, _);
//@ ensures chars(buf, length, n_times(c, length)) &*& length >= 0 &*& chars(buf, length, _);
{
    for (int i = 0; i < length; i++)
    //@ requires i <= length &*& chars_(buf + i, length - i, ?cs0);
    //@ ensures buf[old_i..length] |-> n_times(c, length - old_i);
    {
        buf[i] = c;
        // @ assert chars(buf + i, length - i, _);
        // @ close chars(buf + i, 1, n_times(c, 1));
        // @ close chars(buf, i + 1, n_times(c, i + 1));
    }
    //@ close chars(buf, length, n_times(c, length));
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
