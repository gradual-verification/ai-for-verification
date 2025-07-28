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
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}


/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.

This function ensures nothing. 
*/
bool is_whitespace(int c)
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
{
	tokenizer->lastread = -2;
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_skip_whitespace function reads and drops all the whitespace characters that are encountered sequentially by the tokenizer.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	{
		tokenizer_drop(tokenizer);
	}
}

