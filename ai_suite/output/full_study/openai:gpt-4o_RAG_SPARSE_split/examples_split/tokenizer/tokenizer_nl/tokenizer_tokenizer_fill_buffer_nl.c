#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

// Forward declaration of charreader function type
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
    (lastread == -2 ? true : -128 <= lastread && lastread <= 127) &*&
    string_buffer(buffer);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
/*@
requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer) &*&
         lastread == -2 &*&
         is_charreader(reader) == true;
ensures tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer) &*&
        (new_lastread == -2 ? true : -128 <= new_lastread && new_lastread <= 127);
@*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
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