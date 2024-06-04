/*@

fixpoint_auto list<t> n_times<t>(t x, int count) {
    return count == 0 ? nil : cons(x, n_times(x, count - 1));
}

@*/
/**
 * Function: fill
 *
 * This function fills a buffer with a specified character up to a given length.
 *
 * Inputs:
 * - buf: A pointer to a character buffer.
 * - length: An integer specifying the number of positions in the buffer to fill.
 * - c: A character that will be used to fill the buffer.
 *
 *
 * Behavior:
 * - The function iterates from 0 to length - 1.
 * - In each iteration, it assigns the character c to the current position in the buffer.
 * - The loop invariant ensures that at any point during the loop, the portion of the buffer that has been processed is correctly filled with the character c.
 */
void fill(char *buf, int length, char c)

{
    for (int i = 0; i < length; i++)
  
    {
        buf[i] = c;
    }
}
