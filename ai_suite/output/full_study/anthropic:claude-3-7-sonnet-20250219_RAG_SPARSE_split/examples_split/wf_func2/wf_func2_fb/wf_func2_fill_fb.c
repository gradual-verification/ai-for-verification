/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/


// TODO: make this function pass the verification
void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _;
//@ ensures buf[..length] |-> n_times(c, length);
{
    /*@
    // Loop invariant: the first i elements are filled with c, the rest are arbitrary
    for (int i = 0; ; i++)
        requires buf[0..i] |-> n_times(c, i) &*& buf[i..length] |-> _;
        ensures buf[0..length] |-> n_times(c, length);
    @*/
    for (int i = 0; i < length; i++)
    {
        //@ open chars(buf + i, _, _);
        buf[i] = c;
        //@ close chars(buf + i, 1, cons(c, nil));
        //@ chars_join(buf);
    }
}