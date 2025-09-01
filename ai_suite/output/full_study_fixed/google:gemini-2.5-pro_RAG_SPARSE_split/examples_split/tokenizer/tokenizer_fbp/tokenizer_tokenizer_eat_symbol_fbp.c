#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

typedef int charreader();
    //@ requires true;
    //@ ensures true;


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate Tokenizer(struct tokenizer* t, list<char> cs) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*& lastread >= -128 &*& lastread <= 127 &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, cs);

predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*& lastread >= -128 &*& lastread <= 127 &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;
@*/


void tokenizer_fill_buffer(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer, ?cs);
 //@ ensures Tokenizer(tokenizer, cs);
{
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
}


int tokenizer_peek(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer, ?cs);
 //@ ensures Tokenizer(tokenizer, cs);
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}


int tokenizer_next_char(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer, ?cs);
 //@ ensures Tokenizer(tokenizer, cs) &*& result >= -128 && result <= 127;
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	return c;
}


void string_buffer_append_char(struct string_buffer *buffer, char c)
 //@ requires string_buffer(buffer, ?bcs);
 //@ ensures string_buffer(buffer, append(bcs, cons(c, nil)));
{
	char cc = c;
	string_buffer_append_chars(buffer, &cc, 1);
}


bool is_symbol_char(int c)
 //@ requires true;
 //@ ensures true;
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}


// TODO: make this function pass the verification
int tokenizer_eat_symbol(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer, _);
 //@ ensures Tokenizer(tokenizer, _);
{
	for (;;)
		//@ invariant Tokenizer(tokenizer, _);
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) break;
		
		result = tokenizer_next_char(tokenizer);
		
		//@ open Tokenizer(tokenizer, ?cs);
		//@ assert tokenizer->buffer |-> ?b;
		string_buffer_append_char(b, (char)result);
		//@ close Tokenizer(tokenizer, _);
	}

	return 'S';
}