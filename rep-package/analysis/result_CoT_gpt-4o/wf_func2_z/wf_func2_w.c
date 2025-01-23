/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

void fill(char *buf, int length, char c)
//@ requires length >= 0 &*& chars(buf, length, _);
//@ ensures chars(buf, length, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ requires i <= length &*& chars_(buf + i, length - i, ?cs0);
    //@ ensures buf[old_i..length] |-> n_times(c, length - old_i);
    {
        // @ open chars(buf, length, _);
        buf[i] = c;
        // @ close chars(buf, length, _);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
