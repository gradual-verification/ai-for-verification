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
// The Tokenizer predicate was originally declared as precise (with a ';'), but its body was not,
// because `string_buffer(b, _)` has an undetermined output parameter.
// The semicolon has been removed to declare it as a non-precise predicate.
predicate Tokenizer(struct tokenizer* t) =
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
typedef int charreader();
    //@ requires true;
    //@ ensures result == EOF || (0 <= result && result <= 255);
