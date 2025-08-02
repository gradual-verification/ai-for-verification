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
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer is freed.
*/
//@ predicate tokenizer(struct tokenizer *tokenizer, struct string_buffer *buffer) = 
//@     tokenizer->next_char |-> _ &*&
//@     tokenizer->lastread |-> _ &*&
//@     tokenizer->lasttoken |-> _ &*&
//@     tokenizer->buffer |-> buffer &*&
//@     string_buffer(buffer, _);

void tokenizer_dispose(struct tokenizer *tokenizer)
    //@ requires tokenizer(tokenizer, ?buffer);
    //@ ensures emp;
{
    //@ open tokenizer(tokenizer, buffer);
    string_buffer_dispose(tokenizer->buffer);
    free(tokenizer);
}