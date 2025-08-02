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
    is_charreader(reader) == true &*&
    (-2 <= lastread && lastread <= 127) &*&
    string_buffer(buffer, ?cs);
@*/

/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
//@ ensures tokenizer(tokenizer, reader, lastread == -2 ? result : lastread, lasttoken, buffer) &*& -1 <= result && result <= 127;
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
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
//@ ensures tokenizer(tokenizer, reader, -2, lasttoken, buffer) &*& -1 <= result && result <= 127;
{
	int c;
    
    //@ open tokenizer(tokenizer, reader, lastread, lasttoken, buffer);
	tokenizer_fill_buffer(tokenizer);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
    //@ close tokenizer(tokenizer, reader, -2, lasttoken, buffer);
	return c;
}