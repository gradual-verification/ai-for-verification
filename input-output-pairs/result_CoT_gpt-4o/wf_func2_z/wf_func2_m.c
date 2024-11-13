/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

predicate valid_buffer(char *buf, int length) = 
    chars(buf, length, _);

@*/

void fill(char *buf, int length, char c)
//@ requires valid_buffer(buf, length);
//@ ensures chars(buf, length, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i && i <= length && chars(buf, length, n_times(c, i) ++ n_times('_', length - i));
    {
        //@ open chars(buf, length, _);
        buf[i] = c;
        //@ close chars(buf, length, _);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
