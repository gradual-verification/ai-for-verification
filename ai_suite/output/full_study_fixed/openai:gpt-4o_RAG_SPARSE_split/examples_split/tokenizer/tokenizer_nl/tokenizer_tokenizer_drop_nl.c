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

//@ predicate tokenizer(struct tokenizer* tokenizer, charreader* next_char, int lastread, int lasttoken, struct string_buffer* buffer) =
//@     tokenizer->next_char |-> next_char &*&
//@     tokenizer->lastread |-> lastread &*&
//@     tokenizer->lasttoken |-> lasttoken &*&
//@     tokenizer->buffer |-> buffer &*&
//@     string_buffer(buffer, _);

// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(tokenizer, ?next_char, ?lastread, ?lasttoken, ?buffer);
//@ ensures tokenizer(tokenizer, next_char, -2, lasttoken, buffer);
void tokenizer_drop(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?next_char, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, next_char, -2, lasttoken, buffer);
{
    tokenizer->lastread = -2;
}