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
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer is freed.
*/
//@ predicate tokenizer(struct tokenizer *tokenizer, charreader *next_char, int lastread, int lasttoken, list<char> buffer_contents) =
//@     tokenizer->next_char |-> next_char &*&
//@     tokenizer->lastread |-> lastread &*&
//@     tokenizer->lasttoken |-> lasttoken &*&
//@     tokenizer->buffer |-> ?buffer &*&
//@     string_buffer(buffer, buffer_contents) &*&
//@     malloc_block_tokenizer(tokenizer);

void tokenizer_dispose(struct tokenizer *tokenizer)
    //@ requires tokenizer(tokenizer, ?next_char, ?lastread, ?lasttoken, ?buffer_contents);
    //@ ensures emp;
{
    string_buffer_dispose(tokenizer->buffer);
    free(tokenizer);
}