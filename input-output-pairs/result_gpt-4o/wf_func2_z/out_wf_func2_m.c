#include <stddef.h>

/*@
fixpoint list<char> n_times(char x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

predicate buffer(char *buf; list<char> contents) = 
    array_slice(buf, 0, length(contents), contents);

fixpoint int length<t>(list<t> lst) {
    switch(lst) { case nil: return 0; case cons(h, t): return 1 + length(t); }
}
@*/

void fill(char *buf, int length, char c)
    //@ requires buffer(buf, ?contents) &*& length(contents) == length;
    //@ ensures buffer(buf, n_times(c, length));
{
    for (int i = 0; i < length; i++)
    //@ invariant buffer(buf, n_times(c, i) + drop(i, contents));
    {
        buf[i] = c;
        //@ close buffer(buf, cons(c, n_times(c, i)));
        //@ assert drop(i, contents) == [_] drop(i, contents);
        //@ assert buffer(buf, n_times(c, i+1) + drop(i+1, contents));
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
