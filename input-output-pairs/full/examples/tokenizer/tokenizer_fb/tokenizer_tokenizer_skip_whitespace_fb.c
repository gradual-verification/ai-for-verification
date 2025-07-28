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
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, _);

predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;
@*/


int tokenizer_peek(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}


bool is_whitespace(int c)
 //@ requires true;
 //@ ensures true;
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


void tokenizer_drop(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	tokenizer->lastread = -2;
}


// TODO: make this function pass the verification
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	{
		tokenizer_drop(tokenizer);
	}
}

