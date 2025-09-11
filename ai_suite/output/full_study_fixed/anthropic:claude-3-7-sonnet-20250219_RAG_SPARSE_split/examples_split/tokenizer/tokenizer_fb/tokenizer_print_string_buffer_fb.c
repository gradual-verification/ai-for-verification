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
	

void print_string_buffer(struct string_buffer *buffer)
	//@ requires [?f]string_buffer(buffer, ?cs);
	//@ ensures [f]string_buffer(buffer, cs);
{
	int n = string_buffer_get_length(buffer);
	char *pcs = string_buffer_get_chars(buffer);
	int i;
	//@ open [f]string_buffer_minus_chars(buffer, pcs, n);
	for (i = 0; i < n; i++)
	{
		//@ assert [f]chars(pcs, n, cs);
		//@ chars_split(pcs, i);
		//@ chars_split(pcs + i, 1);
		putchar(pcs[i]);
		//@ chars_join(pcs + i);
		//@ chars_join(pcs);
	}
	//@ string_buffer_merge_chars(buffer);
}