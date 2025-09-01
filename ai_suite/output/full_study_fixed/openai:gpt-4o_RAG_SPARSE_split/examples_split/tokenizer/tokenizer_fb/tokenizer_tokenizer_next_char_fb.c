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

void tokenizer_fill_buffer(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
    if (tokenizer->lastread == -2)
    {
        charreader *reader = tokenizer->next_char;
        int result = reader();
        if (result < -128 || result > 127)
            abort();
        tokenizer->lastread = result;
    }
}

// TODO: make this function pass the verification
int tokenizer_next_char(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
    int c;

    tokenizer_fill_buffer(tokenizer);
    c = tokenizer->lastread;
    tokenizer->lastread = -2;
    return c;
}