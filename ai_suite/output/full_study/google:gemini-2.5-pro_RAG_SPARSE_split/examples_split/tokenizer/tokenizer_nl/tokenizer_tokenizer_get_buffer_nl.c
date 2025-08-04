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
//@ predicate_family is_charreader(void* f)();

/*@
predicate tokenizer(struct tokenizer *t; charreader *next_char, int lastread, int lasttoken, struct string_buffer *buffer, list<char> buffer_cs) =
    t->next_char |-> next_char &*&
    is_charreader(next_char)() &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    string_buffer(buffer, buffer_cs) &*&
    malloc_block_tokenizer(t);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_get_buffer function returns the buffer of a given tokenizer

It needs to make sure that the given tokenizer preserves its property of tokenizer, and 
the return value is a string buffer.
*/
struct string_buffer *tokenizer_get_buffer(struct tokenizer *tokenizer)
    //@ requires [?f]tokenizer(tokenizer, ?nc, ?lr, ?lt, ?b, ?cs);
    //@ ensures [f]tokenizer(tokenizer, nc, lr, lt, b, cs) &*& result == b;
{
    return tokenizer->buffer;
}