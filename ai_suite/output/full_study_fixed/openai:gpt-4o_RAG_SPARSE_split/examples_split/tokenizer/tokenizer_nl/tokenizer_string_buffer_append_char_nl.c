#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();


struct tokenizer
{
    charreader*           next_char;
    int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
    int                   lasttoken; // the last token parsed
    struct string_buffer* buffer;
};

// TODO: make this function pass the verification
/***
 * Description:
The string_buffer_append_char function appends a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
//@ requires string_buffer(buffer, ?bcs) &*& character(&c, ?cc);
//@ ensures string_buffer(buffer, append(bcs, {cc})) &*& character(&c, cc);
void string_buffer_append_char(struct string_buffer *buffer, char c)
{
    char cc = c;
    //@ open string_buffer(buffer, bcs);
    string_buffer_append_chars(buffer, &cc, 1);
    //@ close string_buffer(buffer, append(bcs, {cc}));
}