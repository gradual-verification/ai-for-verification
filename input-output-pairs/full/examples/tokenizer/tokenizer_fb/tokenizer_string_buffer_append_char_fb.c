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


// TODO: make this function pass the verification
void string_buffer_append_char(struct string_buffer *buffer, char c)
 //@ requires string_buffer(buffer, _);
 //@ ensures string_buffer(buffer, _);
{
	char cc = c;
	string_buffer_append_chars(buffer, &cc, 1);
}

