#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
// Predicate for charreader function
predicate charreader_function(charreader* reader;) = 
    is_charreader(reader) == true;

// Predicate for tokenizer structure
predicate tokenizer(struct tokenizer* tokenizer;) =
    tokenizer != 0 &*&
    tokenizer->next_char |-> ?reader &*& 
    charreader_function(reader) &*&
    tokenizer->lastread |-> ?lastread &*&
    tokenizer->lasttoken |-> ?lasttoken &*&
    tokenizer->buffer |-> ?buffer &*&
    string_buffer(buffer, ?cs) &*&
    malloc_block_tokenizer(tokenizer);
@*/

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
The tokenizer_create function creates a tokenizer given a charreader.

It needs to make sure that the returned tokenizer preserves its property of tokenizer. 
*/
struct tokenizer* tokenizer_create(charreader* reader)
//@ requires charreader_function(reader);
//@ ensures tokenizer(result);
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
	//@ close tokenizer(tokenizer);
	return tokenizer;
}