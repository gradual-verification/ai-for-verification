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
// Helper predicate for the main struct fields, excluding lastread.
predicate Tokenizer_guts(struct tokenizer* t) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, _);

// The main predicate, allowing lastread to be -2.
predicate Tokenizer(struct tokenizer* t;) =
  Tokenizer_guts(t) &*&
  t->lastread |-> ?lastread &*& (lastread >= -128 && lastread <= 127 || lastread == -2);

// Helper predicate for the main struct fields, excluding lastread and buffer.
predicate Tokenizer_guts_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  malloc_block_tokenizer(t) &*&
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;

// The predicate for a tokenizer with an externalized buffer, allowing lastread to be -2.
predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  Tokenizer_guts_minus_buffer(t, buffer) &*&
  t->lastread |-> ?lastread &*& (lastread >= -128 && lastread <= 127 || lastread == -2);
@*/


void tokenizer_fill_buffer(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer_guts(tokenizer) &*& tokenizer->lastread |-> ?lr &*& lr >= -128 &*& lr <= 127;
{
	//@ open Tokenizer(tokenizer);
	//@ open Tokenizer_guts(tokenizer);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        //@ assert is_charreader(reader) == true;
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
	//@ close Tokenizer_guts(tokenizer);
}


// TODO: make this function pass the verification
int tokenizer_next_char(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer) &*& result >= -128 && result <= 127;
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open Tokenizer_guts(tokenizer);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ close Tokenizer(tokenizer);
	return c;
}