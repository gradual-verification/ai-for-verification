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

/*@
// A predicate for the tokenizer struct.
// It holds the tokenizer's state, including the last token and the buffer contents.
predicate tokenizer(struct tokenizer *t; int lasttoken, list<char> buffer_cs) =
    t->next_char |-> _ &*&
    t->lastread |-> _ &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> ?buffer &*&
    string_buffer(buffer, buffer_cs) &*&
    malloc_block_tokenizer(t);
@*/


/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();


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
	for (int i = 0; i < n; i++)
	    //@ invariant [f]string_buffer_minus_chars(buffer, pcs, n) &*& [f]chars(pcs, n, cs) &*& 0 <= i &*& i <= n;
	{
		putchar(pcs[i]);
	}
	string_buffer_merge_chars(buffer);
}


// TODO: make this function pass the verification
/***
 * Description:
The print_token function prints the last token of of a tokenizer by reading its lasttoken field and prints a readable content of the token.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void print_token(struct tokenizer* tokenizer)
    //@ requires [?f]tokenizer(tokenizer, ?lasttoken, ?cs);
    //@ ensures [f]tokenizer(tokenizer, lasttoken, cs);
{
	//@ open [f]tokenizer(tokenizer, lasttoken, cs);
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
	//@ close [f]tokenizer(tokenizer, lasttoken, cs);
}