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

typedef int charreader();
    //@ requires true;
    //@ ensures true;

// TODO: make this function pass the verification
struct tokenizer* tokenizer_create(charreader* reader)
 //@ requires is_charreader(reader) == true;
 //@ ensures Tokenizer(result);
{
    struct tokenizer* tokenizer;
    struct string_buffer *buffer;
    
    tokenizer = (struct tokenizer*) malloc( sizeof( struct tokenizer ) );
    if ( tokenizer == 0 ) abort();
    tokenizer->lastread = -2;
    tokenizer->lasttoken = 0;
    tokenizer->next_char = reader;
    buffer = create_string_buffer();
    tokenizer->buffer = buffer;
    //@ close Tokenizer(tokenizer);
    return tokenizer;
}