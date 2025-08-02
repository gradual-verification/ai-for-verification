#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
predicate tokenizer(struct tokenizer* tokenizer, charreader* reader, struct string_buffer* buffer) =
    tokenizer != 0 &*&
    tokenizer->next_char |-> reader &*&
    tokenizer->lastread |-> -2 &*&
    tokenizer->lasttoken |-> 0 &*&
    tokenizer->buffer |-> buffer &*&
    malloc_block_tokenizer(tokenizer) &*&
    string_buffer(buffer, nil);
@*/

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
The tokenizer_create function creates a tokenizer given a charreader.

It needs to make sure that the returned tokenizer preserves its property of tokenizer. 
*/
/*@
requires true;
ensures result == 0 ? true : tokenizer(result, reader, ?buffer);
@*/
struct tokenizer* tokenizer_create(charreader* reader)
{
    struct tokenizer* tokenizer;
    struct string_buffer *buffer;
    
    tokenizer = (struct tokenizer*) malloc( sizeof( struct tokenizer ) );
    if ( tokenizer == 0 ) abort();
    tokenizer->lastread = -2;
    tokenizer->lasttoken = 0;
    tokenizer->next_char = reader;
    buffer = create_string_buffer();
    tokenizer->buffer = buffer;
    return tokenizer;
}