#include <stdlib.h>
#include "vcc.h"

/*@
predicate buffer(char *buf, int length;) =
    chars(buf, length, ?cs) &*& length >= 0;
@*/

/*@
requires buffer(buf, length);
requires length >= 0;
assigns buf[0..length-1];
ensures buffer(buf, length) &*& chars(buf, length, ?cs) &*& all_eq(cs, c);
@*/
void fill(char *buf, int length, char c)
    //@ requires buffer(buf, length);
    //@ ensures buffer(buf, length);
{
    //@ closechars(buf, length, _);
    
    for (int i = 0; i < length; i++)
        //@ invariant chars(buf, length, ?cs1) &*& 0 <= i <= length;
    {
        buf[i] = c;
    }
    
    //@ openchars(buf, length, _);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
