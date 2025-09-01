#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
predicate tokenizer(struct tokenizer* tokenizer, charreader* reader, int lastread, int lasttoken, struct string_buffer* buffer) =
    tokenizer->next_char |-> reader &*&
    tokenizer->lastread |-> lastread &*&
    tokenizer->lasttoken |-> lasttoken &*&
    tokenizer->buffer |-> buffer;
@*/

struct tokenizer
{
    charreader*           next_char;
    int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
    int                   lasttoken; // the last token parsed
    struct string_buffer* buffer;
};

/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
/*@
requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
ensures tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer) &*&
        (lastread == -2 ? (new_lastread >= -128 && new_lastread <= 127) : new_lastread == lastread);
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

/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
/*@
requires tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer);
ensures tokenizer(tokenizer, reader, -2, lasttoken, buffer) &*&
        result == lastread;
@*/
int tokenizer_next_char(struct tokenizer* tokenizer)
{
    int c;

    tokenizer_fill_buffer(tokenizer);
    c = tokenizer->lastread;
    tokenizer->lastread = -2;
    return c;
}