#include "stdio.h"
#include "stdlib.h"
#include "../stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // -1 = EOF, -2 = empty buffer
	int                   lasttoken;
	struct string_buffer* buffer;
};

/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and update the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
{
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
		tokenizer->lastread = result;
	}
}

/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
int tokenizer_peek(struct tokenizer* tokenizer)
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}

/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
void tokenizer_drop(struct tokenizer* tokenizer)
{
	tokenizer->lastread = -2;
}

/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	return c;
}

/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.
*/
bool is_whitespace(int c)
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

/***
 * Description:
The tokenizer_skip_whitespace function reads and drops all the whitespace characters that are encountered sequentially by the tokenizer.
If it peeks a non-whitespace character, it exits the loop and function.

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	{
		tokenizer_drop(tokenizer);
	}
}

/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.
*/
bool is_digit(int c)
{
	return c >= '0' && c <= '9';
}

/***
 * Description:
The string_buffer_append_char function append a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void string_buffer_append_char(struct string_buffer *buffer, char c)
{
	char cc = c;
	string_buffer_append_chars(buffer, &cc, 1);
}

/***
 * Description:
The tokenizer_eat_number function reads all the digit characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and returns the token that represents digit.

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
int tokenizer_eat_number(struct tokenizer* tokenizer)
{
	for (;;)
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);
		isDigit = is_digit(result);
		if ( !isDigit ) break;
		
	    result = tokenizer_next_char(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
	}

	return '0';
}

/***
 * Description:
The is_symbol_char function checks whether a given character in integer means a symbol in ASCII.
*/
bool is_symbol_char(int c)
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}

/***
 * Description:
The tokenizer_eat_symbol function reads all the ASCII symbol characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and return the token that represents symbol.

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
int tokenizer_eat_symbol(struct tokenizer* tokenizer)
{
	for (;;)
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) break;
		
		result = tokenizer_next_char(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
	}

	return 'S';
}

/***
 * Description:
The tokenizer_next function gets the next token of the tokenizer by reading the stream sequentially, assigning the token to lasttoken field, and returning it.

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
int tokenizer_next(struct tokenizer* tokenizer)
{
	int c;
	int token;

	string_buffer_clear(tokenizer->buffer);
	tokenizer_skip_whitespace(tokenizer);

	c = tokenizer_peek(tokenizer);

	if ( c == '(' || c == ')' || c == -1 )
	{
		tokenizer_drop(tokenizer);
		token = c;
	}
	else if ( is_digit(c) )
	{
		
		token = tokenizer_eat_number(tokenizer);
	}
	else if ( is_symbol_char(c) )
	{
		token = tokenizer_eat_symbol(tokenizer);
	}
	else
	{
		tokenizer_drop(tokenizer);
		token = 'B'; // bad character
	}
	tokenizer->lasttoken = token;
	return token;
}

/***
 * Description:
The tokenizer_get_buffer function returns the buffer of a given tokenizer

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
struct string_buffer *tokenizer_get_buffer(struct tokenizer *tokenizer)
{
    return tokenizer->buffer;
}

/***
 * Description:
The tokenizer_create function creates a tokenizer given a charreader.

It needs to make sure that the created tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
struct tokenizer* tokenizer_create(charreader* reader)
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

/***
 * Description:
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
void tokenizer_dispose(struct tokenizer *tokenizer)
{
	string_buffer_dispose(tokenizer->buffer);
	free(tokenizer);
}

/***
 * Description:
The print_string_buffer function prints the content in a string buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void print_string_buffer(struct string_buffer *buffer)
{
	int n = string_buffer_get_length(buffer);
	char *pcs = string_buffer_get_chars(buffer);
	int i;
	for (i = 0; i < n; i++)
	{
		putchar(pcs[i]);
	}
}

/***
 * Description:
The print_token function prints the last token of of a tokenizer by reading its lasttoken field and prints a readable content of the token.

It needs to make sure that the given tokenizer preserves its property in its next_char field as a char reader,
and its buffer field as a string buffer.
*/
void print_token(struct tokenizer* tokenizer)
{
	switch ( tokenizer->lasttoken )
	{
	case '(':
		puts("LPAREN");
		break;

	case ')':
		puts("RPAREN");
		break;

	case '0':
		putchar('N');
		print_string_buffer(tokenizer->buffer);
		puts("");
		break;

	case 'S':
		putchar('S');
		print_string_buffer(tokenizer->buffer);
		puts("");
		break;
	
	case 'B':
		puts("BADCHAR");
		break;
	}
}
