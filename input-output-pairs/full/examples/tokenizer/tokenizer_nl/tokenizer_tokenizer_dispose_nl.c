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


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer is freed.
*/
void tokenizer_dispose(struct tokenizer *tokenizer)
{
	string_buffer_dispose(tokenizer->buffer);
	free(tokenizer);
}

