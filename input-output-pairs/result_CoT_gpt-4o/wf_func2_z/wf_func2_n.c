/*@

predicate buffer(char *buf, int length, list<char> contents) =
    length == 0 ?
        contents == nil :
        // Represent the buffer as a list holding its contents
        chars(buf, length, ?cs) &*&
        contents == cs;

@*/

/**

* Description:

The `fill` function fills a buffer with a specified character up to a given length.

@param buf - A pointer to a character buffer.
@param length - An integer specifying the number of positions in the buffer to fill.
@param c - A character that will be used to fill the buffer.

The behavior goes below:
The function iterates from 0 to length - 1.
In each iteration, it assigns the character c to the current position in the buffer.

*/

/*@
requires buffer(buf, length, ?contents) &*& 0 <= length &*& INT_MIN <= length &*& length <= INT_MAX;
ensures buffer(buf, length, ?new_contents) &*& new_contents == repeat(c, length);
@*/
void fill(char *buf, int length, char c)
    //@ requires buffer(buf, length, ?contents) &*& 0 <= length &*& INT_MIN <= length &*& length <= INT_MAX;
    //@ ensures buffer(buf, length, ?new_contents) &*& new_contents == repeat(c, length);
{
    //@ open buffer(buf, length, contents);
    for (int i = 0; i < length; i++)
        //@ invariant chars(buf, length, ?cs) &*& i <= length &*& cs == append(repeat(c, i), drop(i, contents));
    {
        buf[i] = c;
        //@ open chars(buf, length, cs);
        //@ close chars(buf, length, update(i, c, cs));
    }
    //@ close buffer(buf, length, repeat(c, length));
}

int main()
    //@ requires true;
    //@ ensures true;
{
    return 0;
}
