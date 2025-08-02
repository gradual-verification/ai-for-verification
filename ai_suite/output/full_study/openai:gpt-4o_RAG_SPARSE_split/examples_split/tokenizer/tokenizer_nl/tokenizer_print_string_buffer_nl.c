#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

struct tokenizer
{
    charreader*           next_char;
    int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
    int                   lasttoken; // the last token parsed
    struct string_buffer* buffer;
};

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

// TODO: make this function pass the verification
/***
 * Description:
The print_string_buffer function prints the content in a string buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void print_string_buffer(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs);
{
    int n = string_buffer_get_length(buffer);
    char *pcs = string_buffer_get_chars(buffer);
    int i;
    for (i = 0; i < n; i++)
        //@ invariant string_buffer_minus_chars(buffer, pcs, n) &*& chars(pcs, n, cs) &*& 0 <= i &*& i <= n;
    {
        putchar(pcs[i]);
    }
    //@ string_buffer_merge_chars(buffer);
}