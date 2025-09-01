#include "stdio.h"
#include "stdlib.hh"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires true;
    //@ ensures true;


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer *t) =
    t->next_char |-> ?f &*& is_charreader(f) == true &*&
    t->lastread |-> _ &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?b &*& string_buffer(b, _) &*&
    malloc_block_tokenizer(t);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer is freed.
*/
void tokenizer_dispose(struct tokenizer *tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures true;
{
    //@ open tokenizer(tokenizer);
	string_buffer_dispose(tokenizer->buffer);
	free(tokenizer);
}