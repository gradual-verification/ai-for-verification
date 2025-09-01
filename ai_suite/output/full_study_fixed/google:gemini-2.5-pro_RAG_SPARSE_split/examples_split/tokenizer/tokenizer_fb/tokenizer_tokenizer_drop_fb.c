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
// The original Tokenizer predicate was ill-formed.
// We redefine it here with output parameters to accurately model its state.
predicate Tokenizer(struct tokenizer* t; int lastread, int lasttoken, list<char> cs) =
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> lastread &*&
  t->lasttoken |-> lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, cs);

predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;
@*/
    

// TODO: make this function pass the verification
void tokenizer_drop(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer, ?lastread, ?lasttoken, ?cs);
 //@ ensures Tokenizer(tokenizer, -2, lasttoken, cs);
{
	tokenizer->lastread = -2;
}