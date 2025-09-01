#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
typedef int charreader_t();
    requires true;
    ensures true;
@*/

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer *t; charreader_t *next_char, int lastread, int lasttoken, struct string_buffer* buffer) =
    t->next_char |-> next_char &*& is_charreader_t(next_char) == true &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    malloc_block_tokenizer(t);
@*/


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
		putchar(pcs[i]);
	}
    //@ string_buffer_merge_chars(buffer);
}


// TODO: make this function pass the verification
/***
 * Description:
The print_token function prints the last token of of a tokenizer by reading its lasttoken field and prints a readable content of the token.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void print_token(struct tokenizer* tokenizer)
    //@ requires [?f]tokenizer(tokenizer, ?nc, ?lr, ?lt, ?buf) &*& [?g]string_buffer(buf, ?cs);
    //@ ensures [f]tokenizer(tokenizer, nc, lr, lt, buf) &*& [g]string_buffer(buf, cs);
{
    //@ open [f]tokenizer(tokenizer, nc, lr, lt, buf);
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
    //@ close [f]tokenizer(tokenizer, nc, lr, lt, buf);
}