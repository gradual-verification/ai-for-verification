#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer *tokenizer;) =
    tokenizer->next_char |-> ?reader &*& 
    is_charreader(reader) == true &*&
    tokenizer->lastread |-> ?lastread &*& 
    (-2 <= lastread && lastread <= 127) &*&
    tokenizer->lasttoken |-> ?lasttoken &*&
    tokenizer->buffer |-> ?buffer &*& 
    string_buffer(buffer, ?cs) &*&
    malloc_block_tokenizer(tokenizer);
@*/

/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer);
//@ ensures tokenizer(tokenizer);
{
	if ( tokenizer->lastread == -2 )
	{
	    //@ open tokenizer(tokenizer);
	    charreader *reader = tokenizer->next_char;
	    int result = reader();
		if (result < -128 || result > 127)
			abort();
		tokenizer->lastread = result;
		//@ close tokenizer(tokenizer);
	}
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer);
//@ ensures tokenizer(tokenizer) &*& result == tokenizer->lastread &*& -2 <= result &*& result <= 127;
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer);
	int result = tokenizer->lastread;
	//@ close tokenizer(tokenizer);
	return result;
}


/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer);
//@ ensures tokenizer(tokenizer);
{
    //@ open tokenizer(tokenizer);
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer);
}


/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.

This function ensures nothing. 
*/
bool is_whitespace(int c)
//@ requires true;
//@ ensures true;
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_skip_whitespace function reads and drops all the whitespace characters that are encountered sequentially by the tokenizer.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer);
//@ ensures tokenizer(tokenizer);
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	{
		tokenizer_drop(tokenizer);
	}
}