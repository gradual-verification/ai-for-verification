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

void tokenizer_fill_buffer(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
    if ( tokenizer->lastread == -2 )
    {
        charreader *reader = tokenizer->next_char;
        int result = reader();
        if (result < -128 || result > 127)
            abort();
        tokenizer->lastread = result;
    }
}

int tokenizer_peek(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
    tokenizer_fill_buffer(tokenizer);
    return tokenizer->lastread;
}

int tokenizer_next_char(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer) &*& result >= -128 && result <= 127;
{
    int c;

    tokenizer_fill_buffer(tokenizer);
    c = tokenizer->lastread;
    tokenizer->lastread = -2;
    return c;
}

bool is_digit(int c)
 //@ requires true;
 //@ ensures true;
{
    return c >= '0' && c <= '9';
}

void string_buffer_append_char(struct string_buffer *buffer, char c)
 //@ requires string_buffer(buffer, _);
 //@ ensures string_buffer(buffer, _);
{
    char cc = c;
    string_buffer_append_chars(buffer, &cc, 1);
}

// TODO: make this function pass the verification
int tokenizer_eat_number(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
    for (;;)
    {
        int result;
        bool isDigit;
        
        result = tokenizer_peek(tokenizer);
        isDigit = is_digit(result);
        if ( !isDigit ) break;
        
        result = tokenizer_next_char(tokenizer);
        string_buffer_append_char(tokenizer->buffer, (char)result);
    }

    return '0';
}