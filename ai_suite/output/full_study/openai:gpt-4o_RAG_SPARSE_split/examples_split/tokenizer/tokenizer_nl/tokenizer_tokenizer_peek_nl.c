#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

// Forward declaration of charreader function type
typedef int charreader();

// Definition of the tokenizer structure
struct tokenizer
{
    charreader*           next_char;
    int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
    int                   lasttoken; // the last token parsed
    struct string_buffer* buffer;
};

// Predicate to describe the state of a tokenizer
/*@
predicate tokenizer(struct tokenizer* tokenizer, charreader* reader, int lastread, int lasttoken, struct string_buffer* buffer) =
    tokenizer->next_char |-> reader &*&
    tokenizer->lastread |-> lastread &*&
    tokenizer->lasttoken |-> lasttoken &*&
    tokenizer->buffer |-> buffer &*&
    malloc_block_tokenizer(tokenizer) &*&
    (lastread == -2 ? true : -128 <= lastread && lastread <= 127) &*&
    string_buffer(buffer, _);
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
// TODO: make this function pass the verification
int tokenizer_peek(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, reader, result, lasttoken, buffer) &*& -128 <= result && result <= 127;
{
    tokenizer_fill_buffer(tokenizer);
    return tokenizer->lastread;
}