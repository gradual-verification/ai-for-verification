#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// A predicate family to hold the state of a character reader.
// An instance of this predicate family must be defined for each
// function that implements the charreader function type.
// This allows for different kinds of character readers (e.g., from a file,
// from a string in memory, etc.) to be used with the tokenizer.
predicate_family charreader_state(void *f)();
@*/

// TODO: make this function pass the verification
typedef int charreader();
    //@ requires charreader_state(this)();
    //@ ensures charreader_state(this)() &*& (result == EOF || (0 <= result && result <= 255));


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
  charreader_state(nc)() &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, _);

predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
  charreader_state(nc)() &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;
@*/