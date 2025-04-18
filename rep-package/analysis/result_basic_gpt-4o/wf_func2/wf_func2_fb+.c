#include "stdlib.h" // Ensure inclusion of standard library for size_t

/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}


@*/

void fill(char *buf, int length, char c)
//@ requires chars(buf, length, ?oldChars);
//@ ensures chars(buf, length, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ requires i <= length &*& chars_(buf + i, length - i, ?cs0);
    //@ ensures buf[old_i..length] |-> n_times(c, length - old_i);
    {
        buf[i] = c;
        // @ assert chars(buf, i + 1, append(n_times(c, i), cons(c, nil)));
        // @ open chars(buf + i, length - i, drop(i, oldChars));
    }
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
