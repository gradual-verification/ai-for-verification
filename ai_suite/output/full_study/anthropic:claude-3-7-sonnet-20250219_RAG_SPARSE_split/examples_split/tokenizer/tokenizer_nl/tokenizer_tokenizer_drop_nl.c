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

/*@
// Define a predicate for the tokenizer structure
predicate tokenizer(struct tokenizer* t; charreader* reader, int lastread, int lasttoken, struct string_buffer* buffer) =
    t->next_char |-> reader &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    string_buffer(buffer, _);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
//@ ensures tokenizer(tokenizer, reader, -2, lasttoken, buffer);
{
    //@ open tokenizer(tokenizer, reader, lastread, lasttoken, buffer);
    tokenizer->lastread = -2;
    //@ close tokenizer(tokenizer, reader, -2, lasttoken, buffer);
}