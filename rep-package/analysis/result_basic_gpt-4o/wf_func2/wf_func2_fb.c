#include <limits.h>

/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

predicate char_buffer(char *buf, list<char> cs) =
    switch (cs) {
        case nil: return true;
        case cons(c, cs0): return character(buf, c) &*& char_buffer(buf + 1, cs0);
    };


@*/

void fill(char *buf, int length, char c)
//@ requires buf[..length] |-> _ &*& length >= 0 &*& length <= INT_MAX;
//@ ensures buf[..length] |-> n_times(c, length);
{
    // @ char_buffer_split(buf, length);
    for (int i = 0; i < length; i++)
    // @ invariant 0 <= i &*& i <= length &*& char_buffer(buf + i, n_times(c, length - i));
    //@ requires i <= length &*& chars_(buf + i, length - i, ?cs0);
    //@ ensures buf[old_i..length] |-> n_times(c, length - old_i);
    {
        // @ open char_buffer(buf + i, _);
        buf[i] = c;
        // @ assert character(buf + i, c);
        // @ close char_buffer(buf + i, cons(c, nil));
        // @ char_buffer_merge(buf);
    }
    // @ close char_buffer(buf, n_times(c, length));
}

int main()
//@ requires true;
//@ ensures true;
{
    return 0;
}
