#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

// Forward declaration of charreader type
typedef int charreader();

// Structure definition for tokenizer
struct tokenizer
{
    charreader*           next_char;
    int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
    int                   lasttoken; // the last token parsed
    struct string_buffer* buffer;
};

// Predicate for tokenizer structure
/*@
predicate tokenizer(struct tokenizer* tokenizer, charreader* reader, int lastread, int lasttoken, struct string_buffer* buffer) =
    tokenizer->next_char |-> reader &*&
    tokenizer->lastread |-> lastread &*&
    tokenizer->lasttoken |-> lasttoken &*&
    tokenizer->buffer |-> buffer &*&
    malloc_block_tokenizer(tokenizer) &*&
    (lastread == -2 ? true : -128 <= lastread && lastread <= 127);
@*/

// Function to fill the tokenizer buffer
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer) &*& (lastread == -2 ? -128 <= new_lastread && new_lastread <= 127 : new_lastread == lastread);
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

// Function to peek the next character in the tokenizer
int tokenizer_peek(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer) &*& result == new_lastread;
{
    tokenizer_fill_buffer(tokenizer);
    return tokenizer->lastread;
}

// Function to drop the last character in the tokenizer
void tokenizer_drop(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, reader, -2, lasttoken, buffer);
{
    tokenizer->lastread = -2;
}

// Function to check if a character is whitespace
bool is_whitespace(int c)
    //@ requires true;
    //@ ensures true;
{
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

// Function to skip whitespace in the tokenizer
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer) &*& (is_whitespace(new_lastread) == false || new_lastread == -1);
{
    while (is_whitespace(tokenizer_peek(tokenizer)))
    {
        tokenizer_drop(tokenizer);
    }
}