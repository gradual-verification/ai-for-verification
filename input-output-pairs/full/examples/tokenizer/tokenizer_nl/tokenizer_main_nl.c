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
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer is freed.
*/
void tokenizer_dispose(struct tokenizer *tokenizer)
{
	string_buffer_dispose(tokenizer->buffer);
	free(tokenizer);
}


/***
 * Description:
The print_token function prints the last token of of a tokenizer by reading its lasttoken field and prints a readable content of the token.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
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


/***
 * Description:
The tokenizer_create function creates a tokenizer given a charreader.

It needs to make sure that the returned tokenizer preserves its property of tokenizer. 
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
The tokenizer_next function gets the next token of the tokenizer by reading the stream sequentially, assigning the token to lasttoken field, and returning it.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
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


// TODO: make this function pass the verification
/***
 * Description:
The main function tests the functionality of tokenizer operations.
It first creates a tokenizer, then continues reading and printing the tokens,
and finally free the tokenizer.
*/
int main()
{
	struct tokenizer* tokenizer = tokenizer_create(my_getchar);

	for (;;)
	{
		int result = tokenizer_next(tokenizer);
		if (result == -1) break;
		print_token(tokenizer);
	}
	
	tokenizer_dispose(tokenizer);

	puts("The end");
	return 0;
}