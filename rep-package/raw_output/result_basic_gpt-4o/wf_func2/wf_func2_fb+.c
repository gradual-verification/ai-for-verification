#include "stdlib.h" // Ensure inclusion of standard library for size_t

/*@
fixpoint list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

lemma void n_times_length<t>(t x, int count)
    requires count >= 0;
    ensures length(n_times(x, count)) == count;
{
    switch(count) {
        case 0:
        case succ(n):
            n_times_length(x, n);
    }
}
@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, ?oldChars);
//@ ensures chars(buf, length, n_times(c, length));
{
    //@ n_times_length(c, length);
    for (int i = 0; i < length; i++)
    //@ invariant chars(buf, i, n_times(c, i)) &*& chars(buf + i, length - i, drop(i, oldChars));
    {
        buf[i] = c;
        //@ assert chars(buf, i + 1, append(n_times(c, i), cons(c, nil)));
        //@ open chars(buf + i, length - i, drop(i, oldChars));
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
