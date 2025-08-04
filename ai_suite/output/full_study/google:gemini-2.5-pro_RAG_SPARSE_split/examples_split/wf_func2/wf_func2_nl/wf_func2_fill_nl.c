/*@
fixpoint list<char> repeat(char c, int n) {
    return n <= 0 ? nil : cons(c, repeat(c, n - 1));
}
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
    //@ requires chars(buf, length, ?cs) &*& 0 <= length;
    //@ ensures chars(buf, length, repeat(c, length));
{
    for (int i = 0; i < length; i++)
        //@ requires chars(buf + i, length - i, drop(i, cs));
        //@ ensures chars(buf + old_i, length - old_i, repeat(c, length - old_i));
    {
        //@ open chars(buf + i, length - i, drop(i, cs));
        buf[i] = c;
        //@ recursive_call();
        //@ close chars(buf + i, length - i, repeat(c, length - i));
    }
}