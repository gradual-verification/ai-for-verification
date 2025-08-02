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

//@ predicate tokenizer(struct tokenizer* tokenizer;) =
//@     tokenizer->next_char |-> ?next_char &*&
//@     tokenizer->lastread |-> ?lastread &*&
//@     tokenizer->lasttoken |-> ?lasttoken &*&
//@     tokenizer->buffer |-> ?buffer &*&
//@     string_buffer(buffer, _);

/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
// TODO: make this function pass the verification
void tokenizer_drop(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
{
    tokenizer->lastread = -2;
}