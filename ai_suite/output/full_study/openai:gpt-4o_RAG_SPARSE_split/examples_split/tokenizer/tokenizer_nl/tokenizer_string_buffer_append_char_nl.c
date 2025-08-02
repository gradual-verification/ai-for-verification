#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

// TODO: make this function pass the verification
/***
 * Description:
The string_buffer_append_char function appends a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void string_buffer_append_char(struct string_buffer *buffer, char c)
    //@ requires string_buffer(buffer, ?bcs);
    //@ ensures string_buffer(buffer, append(bcs, cons(c, nil)));
{
    char cc = c;
    //@ chars_to_uchars(&cc);
    string_buffer_append_chars(buffer, &cc, 1);
}