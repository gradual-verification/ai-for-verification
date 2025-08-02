/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

// TODO: make this function pass the verification
void fill(char *buf, int length, char c)
//@ requires chars(buf, length, ?cs);
//@ ensures chars(buf, length, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ invariant chars(buf, length, ?cs0) &*& take(i, cs0) == n_times(c, i);
    {
        //@ open chars(buf, length, cs0);
        buf[i] = c;
        //@ close chars(buf + i, 1, cons(c, nil));
        //@ close chars(buf, length, update(i, c, cs0));
    }
}