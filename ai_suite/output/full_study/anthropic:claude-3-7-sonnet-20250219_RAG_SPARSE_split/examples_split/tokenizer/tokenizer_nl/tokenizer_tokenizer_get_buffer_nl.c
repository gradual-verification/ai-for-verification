#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
// Define a predicate for the charreader function pointer
predicate charreader_function(charreader *f) = is_charreader(f) == true;
@*/

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
// Define a predicate for the tokenizer structure
predicate tokenizer(struct tokenizer *t; charreader *reader, int last_read, int last_token, struct string_buffer *buf) =
    t->next_char |-> reader &*&
    t->lastread |-> last_read &*&
    t->lasttoken |-> last_token &*&
    t->buffer |-> buf &*&
    charreader_function(reader) &*&
    string_buffer(buf) &*&
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
/*@
requires tokenizer(tokenizer, ?reader, ?last_read, ?last_token, ?buffer);
ensures tokenizer(tokenizer, reader, last_read, last_token, buffer) &*& result == buffer;
@*/
{
    //@ open tokenizer(tokenizer, reader, last_read, last_token, buffer);
    struct string_buffer *result = tokenizer->buffer;
    //@ close tokenizer(tokenizer, reader, last_read, last_token, buffer);
    return result;
}