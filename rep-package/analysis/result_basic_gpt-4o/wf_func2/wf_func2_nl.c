#include <stdlib.h>
//#include "vcc.h"

/*@
fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}
@*/

/*@
predicate buffer(char *buf, int length;) =
    chars_(buf, length, ?cs) &*& length >= 0;
@*/


void fill(char *buf, int length, char c)
//@ requires buffer(buf, length) &*& length >= 0;
//@ ensures chars(buf, length, n_times(c, length));
{
    // @ closechars(buf, length, _);
    
    for (int i = 0; i < length; i++)
    //@ requires i <= length &*& chars_(buf + i, length - i, ?cs0);
    //@ ensures chars(buf + old_i, length - old_i, n_times(c, length - old_i));
    {
        buf[i] = c;
    }
    
    // @ openchars(buf, length, _);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
