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
void print_string_buffer(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs);
{
    int n = string_buffer_get_length(buffer);
    char *pcs = string_buffer_get_chars(buffer);
    int i;
    for (i = 0; i < n; i++)
    //@ invariant [f]string_buffer_minus_chars(buffer, pcs, n) &*& [f]chars(pcs, n, cs) &*& 0 <= i &*& i <= n;
    {
        putchar(pcs[i]);
        //@ open chars(pcs, n, cs);
        //@ close chars(pcs, n, cs);
    }
    //@ string_buffer_merge_chars(buffer);
}