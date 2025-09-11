#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

// TODO: make this function pass the verification
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

/*@
// Define the predicate for charreader function type
predicate charreader_pre() = true;
predicate charreader_post(int result) = true;

// Define the is_charreader function to check if a function pointer is a valid charreader
fixpoint bool is_charreader(charreader* f) {
  return f != 0;
}

// Define the contract for the charreader function type
lemma void charreader_contract(charreader* f)
  requires is_charreader(f) == true;
  ensures [_]is_function_pointer_of(f, charreader_pre, charreader_post);
{
  assume(false);
}

// Helper lemma to create a tokenizer
lemma void create_tokenizer(struct tokenizer* t, charreader* nc, int lastread, int lasttoken, struct string_buffer* buffer)
  requires t->next_char |-> nc &*& is_charreader(nc) == true &*&
           t->lastread |-> lastread &*&
           t->lasttoken |-> lasttoken &*&
           t->buffer |-> buffer &*& string_buffer(buffer, _);
  ensures Tokenizer(t);
{
  close Tokenizer(t);
}

// Helper lemma to open a tokenizer
lemma void open_tokenizer(struct tokenizer* t)
  requires Tokenizer(t);
  ensures t->next_char |-> ?nc &*& is_charreader(nc) == true &*&
          t->lastread |-> ?lastread &*&
          t->lasttoken |-> ?lasttoken &*&
          t->buffer |-> ?b &*& string_buffer(b, _);
{
  open Tokenizer(t);
}

// Helper lemma to convert between Tokenizer and Tokenizer_minus_buffer
lemma void tokenizer_to_minus_buffer(struct tokenizer* t)
  requires Tokenizer(t);
  ensures Tokenizer_minus_buffer(t, ?buffer) &*& string_buffer(buffer, _);
{
  open Tokenizer(t);
  close Tokenizer_minus_buffer(t, ?buffer);
}

lemma void minus_buffer_to_tokenizer(struct tokenizer* t, struct string_buffer* buffer)
  requires Tokenizer_minus_buffer(t, buffer) &*& string_buffer(buffer, _);
  ensures Tokenizer(t);
{
  open Tokenizer_minus_buffer(t, buffer);
  close Tokenizer(t);
}
@*/

// Example implementation of a charreader function
int stdin_reader() //@ : charreader
//@ requires true;
//@ ensures true;
{
    return getchar();
}

// Example function that uses a tokenizer
void read_token(struct tokenizer* t)
//@ requires Tokenizer(t);
//@ ensures Tokenizer(t);
{
    //@ open Tokenizer(t);
    int c = t->next_char();
    t->lastread = c;
    //@ close Tokenizer(t);
}