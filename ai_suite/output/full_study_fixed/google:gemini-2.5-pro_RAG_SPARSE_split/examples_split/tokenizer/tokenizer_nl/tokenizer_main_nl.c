#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// A charreader is a function that produces characters.
typedef int charreader();
    requires true;
    ensures true;

// Predicate for the tokenizer struct.
predicate tokenizer(struct tokenizer *t) =
    t->next_char |-> ?reader &*&
    t->lastread |-> ?lastread &*&
    t->lasttoken |-> ?lasttoken &*&
    t->buffer |-> ?buffer &*&
    malloc_block_tokenizer(t) &*&
    is_charreader(reader) == true &*&
    string_buffer(buffer, ?cs) &*&
    (lastread == -2 || (-128 <= lastread && lastread <= 127));
@*/

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
	//@ open tokenizer(tokenizer);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
	//@ close tokenizer(tokenizer);
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
	//@ requires tokenizer(tokenizer);
	//@ ensures tokenizer(tokenizer) &*& -128 <= result &*& result <= 127;
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
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
	//@ requires tokenizer(tokenizer);
	//@ ensures tokenizer(tokenizer) &*& -128 <= result &*& result <= 127;
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer);
	return c;
}


/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.

This function ensures nothing. 
*/
bool is_whitespace(int c)
	//@ requires true;
	//@ ensures result == (c == ' ' || c == '\n' || c == '\r' || c == '\t');
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


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
		//@ invariant tokenizer(tokenizer);
	{
		tokenizer_drop(tokenizer);
	}
}


/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.

It ensures nothing.
*/
bool is_digit(int c)
	//@ requires true;
	//@ ensures result == (c >= '0' && c <= '9');
{
	return c >= '0' && c <= '9';
}


/***
 * Description:
The string_buffer_append_char function appends a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void string_buffer_append_char(struct string_buffer *buffer, char c)
	//@ requires string_buffer(buffer, ?cs);
	//@ ensures string_buffer(buffer, append(cs, cons(c, nil)));
{
	char cc = c;
	string_buffer_append_chars(buffer, &cc, 1);
}


/***
 * Description:
The tokenizer_eat_number function reads all the digit characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and returns the token that represents digit.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_eat_number(struct tokenizer* tokenizer)
	//@ requires tokenizer(tokenizer);
	//@ ensures tokenizer(tokenizer) &*& result == '0';
{
	for (;;)
		//@ invariant tokenizer(tokenizer);
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);
		isDigit = is_digit(result);
		if ( !isDigit ) break;
		
	    result = tokenizer_next_char(tokenizer);
		//@ open tokenizer(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
		//@ close tokenizer(tokenizer);
	}

	return '0';
}


/***
 * Description:
The is_symbol_char function checks whether a given character in integer means a symbol in ASCII (except parentheses).

It ensures nothing
*/
bool is_symbol_char(int c)
	//@ requires true;
	//@ ensures result == (c > 32 && c <= 127 && c != '(' && c != ')');
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}


/***
 * Description:
The tokenizer_eat_symbol function reads all the ASCII symbol characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-symbol character, it exits the loop and return the token that represents symbol.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_eat_symbol(struct tokenizer* tokenizer)
	//@ requires tokenizer(tokenizer);
	//@ ensures tokenizer(tokenizer) &*& result == 'S';
{
	for (;;)
		//@ invariant tokenizer(tokenizer);
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) break;
		
		result = tokenizer_next_char(tokenizer);
		//@ open tokenizer(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
		//@ close tokenizer(tokenizer);
	}

	return 'S';
}


/***
 * Description:
The tokenizer_next function gets the next token of the tokenizer by reading the stream sequentially, assigning the token to lasttoken field, and returning it.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next(struct tokenizer* tokenizer)
	//@ requires tokenizer(tokenizer);
	//@ ensures tokenizer(tokenizer);
{
	int c;
	int token;

	//@ open tokenizer(tokenizer);
	string_buffer_clear(tokenizer->buffer);
	//@ close tokenizer(tokenizer);
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
	//@ open tokenizer(tokenizer);
	tokenizer->lasttoken = token;
	//@ close tokenizer(tokenizer);
	return token;
}


/***
 * Description:
The tokenizer_create function creates a tokenizer given a charreader.

It needs to make sure that the returned tokenizer preserves its property of tokenizer. 
*/
struct tokenizer* tokenizer_create(charreader* reader)
	//@ requires is_charreader(reader) == true;
	//@ ensures tokenizer(result);
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
	//@ close tokenizer(tokenizer);
	return tokenizer;
}


/***
 * Description:
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer is freed.
*/
void tokenizer_dispose(struct tokenizer *tokenizer)
	//@ requires tokenizer(tokenizer);
	//@ ensures true;
{
	//@ open tokenizer(tokenizer);
	string_buffer_dispose(tokenizer->buffer);
	free(tokenizer);
}


/***
 * Description:
The print_string_buffer function prints the content in a string buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void print_string_buffer(struct string_buffer *buffer)
	//@ requires [?f]string_buffer(buffer, ?cs);
	//@ ensures [f]string_buffer(buffer, cs);
{
	int n = string_buffer_get_length(buffer);
	char *pcs = string_buffer_get_chars(buffer);
	int i;
	for (i = 0; i < n; i++)
		//@ invariant [f]string_buffer_minus_chars(buffer, pcs, n) &*& [f]chars(pcs, n, cs) &*& 0 <= i &*& i <= n;
	{
		//@ chars_split(pcs, i);
		//@ open chars(pcs + i, n - i, drop(i, cs));
		putchar(pcs[i]);
		//@ close chars(pcs + i, n - i, drop(i, cs));
		//@ chars_join(pcs);
	}
	string_buffer_merge_chars(buffer);
}


/***
 * Description:
The print_token function prints the last token of of a tokenizer by reading its lasttoken field and prints a readable content of the token.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void print_token(struct tokenizer* tokenizer)
	//@ requires [?f]tokenizer(tokenizer);
	//@ ensures [f]tokenizer(tokenizer);
{
	//@ open [f]tokenizer(tokenizer);
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
	//@ close [f]tokenizer(tokenizer);
}


/***
 * Description:
The my_getchar function acts as a char reader and returns an integer read.

It ensures nothing.
*/
int my_getchar() //@ : charreader
	//@ requires true;
	//@ ensures true;
{
	return getchar();
}


// TODO: make this function pass the verification
/***
 * Description:
The main function tests the functionality of tokenizer operations.
It first creates a tokenizer, then continues reading and printing the tokens,
and finally free the tokenizer.
*/
int main() //@ : main
	//@ requires true;
	//@ ensures true;
{
	struct tokenizer* tokenizer = tokenizer_create(my_getchar);

	for (;;)
		//@ invariant tokenizer(tokenizer);
	{
		int result = tokenizer_next(tokenizer);
		if (result == -1) break;
		print_token(tokenizer);
	}
	
	tokenizer_dispose(tokenizer);

	puts("The end");
	return 0;
}