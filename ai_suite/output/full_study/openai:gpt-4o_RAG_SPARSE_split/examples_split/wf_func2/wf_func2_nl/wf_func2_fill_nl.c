#include <stddef.h>
#include <limits.h>

//@ #include "prelude.h"
//@ #include "list.gh"

/*@
predicate chars(char *array, int count; list<char> cs) =
    count == 0 ?
        cs == nil
    :
        character(array, ?c) &*& chars(array + 1, count - 1, ?cs0) &*& cs == cons(c, cs0);
@*/

// TODO: make this function pass the verification
/***
* Description:

The `fill` function fills a buffer with a specified character up to a given length.

@param buf - A pointer to a character buffer.
@param length - An integer specifying the number of positions in the buffer to fill.
@param c - A character that will be used to fill the buffer.

The function makes sure that 0 to length - 1 in buf are filled with c.
*/
void fill(char *buf, int length, char c)
    //@ requires chars(buf, length, ?cs);
    //@ ensures chars(buf, length, ?cs2) &*& length >= 0 &*& cs2 == repeat(c, length);
{
    for (int i = 0; i < length; i++)
        //@ invariant chars(buf, length, ?cs3) &*& 0 <= i &*& i <= length &*& cs3 == append(repeat(c, i), drop(i, cs));
    {
        buf[i] = c;
        //@ open chars(buf + i, length - i, _);
        //@ close chars(buf + i, length - i, _);
    }
}