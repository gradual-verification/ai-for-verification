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
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

