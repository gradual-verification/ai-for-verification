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
predicate Tokenizer(struct tokenizer* t;) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*& lastread >= -128 &*& lastread <= 127 &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, _);

predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*& lastread >= -128 &*& lastread <= 127 &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;
@*/


bool is_symbol_char(int c)
 //@ requires true;
 //@ ensures true;
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}


void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	{
		tokenizer_drop(tokenizer);
	}
}


void tokenizer_drop(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	tokenizer->lastread = -2;
}


bool is_digit(int c)
 //@ requires true;
 //@ ensures true;
{
	return c >= '0' && c <= '9';
}


int tokenizer_eat_symbol(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
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


int tokenizer_eat_number(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
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


int tokenizer_peek(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}


// TODO: make this function pass the verification
int tokenizer_next(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
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

