/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

// TODO: make this function pass the verification
void fill(char *buf, int length, char c)
//@ requires chars_(buf, length, _);
//@ ensures chars(buf, length, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ invariant chars(buf, i, n_times(c, i)) &*& chars_(buf + i, length - i, _);
    {
        //@ open chars_(buf + i, length - i, _);
        buf[i] = c;
        //@ close chars(buf, i + 1, n_times(c, i + 1));
    }
    //@ open chars_(buf + length, 0, _);
}