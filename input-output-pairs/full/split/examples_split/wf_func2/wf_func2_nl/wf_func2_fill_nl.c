

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
{
    for (int i = 0; i < length; i++)
    {
        buf[i] = c;
    }
}