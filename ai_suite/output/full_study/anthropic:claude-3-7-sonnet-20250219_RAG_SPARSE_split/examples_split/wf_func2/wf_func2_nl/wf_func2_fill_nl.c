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
//@ requires buf != 0 &*& chars(buf, length, _);
//@ ensures chars(buf, length, ?cs) &*& all_eq(cs, c) == true;
{
    //@ open chars(buf, length, _);
    for (int i = 0; i < length; i++)
    //@ invariant 0 <= i &*& i <= length &*& buf != 0 &*& chars(buf, i, ?cs1) &*& chars(buf + i, length - i, ?cs2) &*& all_eq(cs1, c) == true;
    {
        buf[i] = c;
        //@ close character(buf + i, c);
    }
    //@ assert chars(buf, length, ?cs);
    //@ assert all_eq(cs, c) == true;
}