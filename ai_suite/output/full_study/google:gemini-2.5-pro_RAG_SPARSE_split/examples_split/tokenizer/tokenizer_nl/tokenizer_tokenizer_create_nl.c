#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// A charreader is a function that reads a character.
// We model this abstractly using predicate families.
// The user of the tokenizer must provide instances for these families.
predicate_family charreader_pre(void* reader)();
predicate_family charreader_post(void* reader)(int char_read);
@*/

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires charreader_pre(this)();
    //@ ensures charreader_post(this)(result);

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer* t; charreader* reader, int lastread, int lasttoken, list<char> buffer_content) =
    t->next_char |-> reader &*&
    is_charreader(reader) == true &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> ?buffer &*&
    string_buffer(buffer, buffer_content) &*&
    malloc_block_tokenizer(t);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_create function creates a tokenizer given a charreader.

It needs to make sure that the returned tokenizer preserves its property of tokenizer. 
*/
struct tokenizer* tokenizer_create(charreader* reader)
    //@ requires is_charreader(reader) == true;
    //@ ensures tokenizer(result, reader, -2, 0, nil);
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