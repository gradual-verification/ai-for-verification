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
The tokenizer_get_buffer function returns the buffer of a given tokenizer

It needs to make sure that the given tokenizer preserves its property of tokenizer, and 
the return value is a string buffer.
*/
//@ predicate tokenizer(struct tokenizer *tokenizer, struct string_buffer *buffer) = 
//@     tokenizer->buffer |-> buffer &*& string_buffer(buffer);

struct string_buffer *tokenizer_get_buffer(struct tokenizer *tokenizer)
    //@ requires tokenizer(tokenizer, ?buffer);
    //@ ensures tokenizer(tokenizer, buffer) &*& result == buffer;
{
    return tokenizer->buffer;
}