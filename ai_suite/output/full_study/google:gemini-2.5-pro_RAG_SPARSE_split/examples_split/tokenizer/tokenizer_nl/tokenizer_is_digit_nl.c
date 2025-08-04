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


// TODO: make this function pass the verification
/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.

It ensures nothing.
*/
/*@
requires true;
ensures result == (c >= '0' && c <= '9');
@*/
bool is_digit(int c)
{
	return c >= '0' && c <= '9';
}