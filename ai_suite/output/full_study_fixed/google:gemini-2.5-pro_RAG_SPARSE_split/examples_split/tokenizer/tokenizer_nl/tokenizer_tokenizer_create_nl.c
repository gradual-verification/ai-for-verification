#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// A predicate family to hold the resources required by a charreader instance.
// This allows different charreader implementations to have different state.
predicate_family charreader_permission(void* reader)();

// A predicate representing a valid, initialized tokenizer.
// It owns the memory for the struct and all associated resources,
// including the string buffer and the permission to call the charreader.
predicate tokenizer(struct tokenizer *t) =
    t->next_char |-> ?reader &*&
    t->lastread |-> -2 &*&
    t->lasttoken |-> 0 &*&
    t->buffer |-> ?buffer &*&
    malloc_block_tokenizer(t) &*&
    string_buffer(buffer, nil) &*&
    is_charreader(reader) == true &*&
    charreader_permission(reader)();
@*/

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires charreader_permission(this)();
    //@ ensures charreader_permission(this)() &*& result >= -1;


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
    //@ requires is_charreader(reader) == true &*& charreader_permission(reader)();
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
	return tokenizer;
}