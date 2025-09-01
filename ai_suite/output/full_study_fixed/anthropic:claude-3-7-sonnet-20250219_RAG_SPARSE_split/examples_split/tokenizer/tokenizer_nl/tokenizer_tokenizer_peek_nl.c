#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

//@ predicate charreader_function(charreader *reader) = is_charreader(reader) == true;

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

//@ predicate tokenizer(struct tokenizer* t; charreader* reader, int lastread, int lasttoken, struct string_buffer* buffer) = t->next_char |-> reader &*& t->lastread |-> lastread &*& t->lasttoken |-> lasttoken &*& t->buffer |-> buffer &*& charreader_function(reader) &*& string_buffer(buffer, ?cs) &*& (lastread == -2 || lastread == -1 || (-128 <= lastread && lastread <= 127));

/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
//@ ensures tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer) &*& (lastread != -2 ? new_lastread == lastread : true);
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


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
//@ ensures tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer) &*& result == new_lastread &*& (new_lastread == -1 || (-128 <= new_lastread && new_lastread <= 127));
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}