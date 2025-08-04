/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

lemma void n_times_append<t>(t x, int c1, int c2)
    requires c1 >= 0 &*& c2 >= 0;
    ensures append(n_times(x, c1), n_times(x, c2)) == n_times(x, c1 + c2);
{
    switch (c1) {
        case 0:
        default:
            n_times_append(x, c1 - 1, c2);
    }
}
@*/


// TODO: make this function pass the verification
void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _;
//@ ensures buf[..length] |-> n_times(c, length);
{
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i &*& i <= length &*& buf[0..i] |-> n_times(c, i) &*& buf[i..length] |-> _;
    {
        buf[i] = c;
        //@ n_times_append(c, i, 1);
    }
}