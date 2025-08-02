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
predicate tokenizer(struct tokenizer* tokenizer;) =
    tokenizer != 0 &*&
    tokenizer->next_char |-> ?reader &*&
    tokenizer->lastread |-> ?lastread &*&
    tokenizer->lasttoken |-> ?lasttoken &*&
    tokenizer->buffer |-> ?buffer &*&
    is_charreader(reader) == true &*&
    (-2 <= lastread && lastread <= 127) &*&
    string_buffer(buffer, ?cs) &*&
    malloc_block_tokenizer(tokenizer);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
/*@
requires tokenizer(tokenizer);
ensures tokenizer(tokenizer);
@*/
{
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
}