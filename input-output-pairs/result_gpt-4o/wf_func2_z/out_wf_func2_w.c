#include <stddef.h>

/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, _);
//@ ensures chars(buf, length, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ invariant chars(buf, length, append(n_times(c, i), ?rest));
    {
        buf[i] = c;
        //@ close chars(buf + i, 1, n_times(c, 1));
        //@ append_assoc(n_times(c, i), n_times(c, 1), rest);
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
