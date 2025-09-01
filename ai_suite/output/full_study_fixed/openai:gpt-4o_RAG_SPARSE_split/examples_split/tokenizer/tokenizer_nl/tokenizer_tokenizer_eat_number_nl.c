#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
predicate tokenizer(struct tokenizer *tokenizer, charreader *next_char, int lastread, int lasttoken, struct string_buffer *buffer) =
    tokenizer->next_char |-> next_char &*&
    tokenizer->lastread |-> lastread &*&
    tokenizer->lasttoken |-> lasttoken &*&
    tokenizer->buffer |-> buffer &*&
    malloc_block_tokenizer(tokenizer) &*&
    (lastread == -2 ? true : -128 <= lastread && lastread <= 127) &*&
    string_buffer(buffer, _);
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
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?next_char, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, next_char, ?new_lastread, lasttoken, buffer) &*& (lastread == -2 ? -128 <= new_lastread && new_lastread <= 127 : new_lastread == lastread);
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
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?next_char, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, next_char, result, lasttoken, buffer) &*& -128 <= result && result <= 127;
{
    tokenizer_fill_buffer(tokenizer);
    return tokenizer->lastread;
}

/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?next_char, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, next_char, -2, lasttoken, buffer) &*& -128 <= result && result <= 127;
{
    int c;

    tokenizer_fill_buffer(tokenizer);
    c = tokenizer->lastread;
    tokenizer->lastread = -2;
    return c;
}

/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.

It ensures nothing.
*/
bool is_digit(int c)
    //@ requires true;
    //@ ensures true;
{
    return c >= '0' && c <= '9';
}

/***
 * Description:
The string_buffer_append_char function appends a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void string_buffer_append_char(struct string_buffer *buffer, char c)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, append(cs, cons(c, nil)));
{
    char cc = c;
    string_buffer_append_chars(buffer, &cc, 1);
}

// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_eat_number function reads all the digit characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and returns the token that represents digit.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_eat_number(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?next_char, ?lastread, ?lasttoken, ?buffer);
    //@ ensures tokenizer(tokenizer, next_char, ?new_lastread, '0', buffer) &*& string_buffer(buffer, ?new_buffer) &*& forall(new_buffer, is_digit);
{
    for (;;)
    {
        int result;
        bool isDigit;
        
        result = tokenizer_peek(tokenizer);
        isDigit = is_digit(result);
        if (!isDigit) break;
        
        result = tokenizer_next_char(tokenizer);
        string_buffer_append_char(tokenizer->buffer, (char)result);
    }

    return '0';
}