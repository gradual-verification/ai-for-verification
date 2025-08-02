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

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
predicate tokenizer(struct tokenizer* tokenizer) =
    tokenizer->next_char |-> ?next_char &*&
    tokenizer->lastread |-> ?lastread &*&
    tokenizer->lasttoken |-> ?lasttoken &*&
    tokenizer->buffer |-> ?buffer &*&
    string_buffer(buffer, _);
@*/

/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
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
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer) &*& result == tokenizer->lastread;
{
    tokenizer_fill_buffer(tokenizer);
    return tokenizer->lastread;
}

/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
{
    tokenizer->lastread = -2;
}

/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
{
    int c;

    tokenizer_fill_buffer(tokenizer);
    c = tokenizer->lastread;
    tokenizer->lastread = -2;
    return c;
}

/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.

This function ensures nothing. 
*/
bool is_whitespace(int c)
    //@ requires true;
    //@ ensures true;
{
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

/***
 * Description:
The tokenizer_skip_whitespace function reads and drops all the whitespace characters that are encountered sequentially by the tokenizer.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
{
    while (is_whitespace(tokenizer_peek(tokenizer)))
    {
        tokenizer_drop(tokenizer);
    }
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

/***
 * Description:
The tokenizer_eat_number function reads all the digit characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and returns the token that represents digit.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_eat_number(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
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

/***
 * Description:
The is_symbol_char function checks whether a given character in integer means a symbol in ASCII (except parentheses).

It ensures nothing
*/
bool is_symbol_char(int c)
    //@ requires true;
    //@ ensures true;
{
    return c > 32 && c <= 127 && c != '(' && c != ')'; 
}

/***
 * Description:
The tokenizer_eat_symbol function reads all the ASCII symbol characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-symbol character, it exits the loop and return the token that represents symbol.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_eat_symbol(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
{
    for (;;)
    {
        int result;
        bool isSymbolChar;
        
        result = tokenizer_peek(tokenizer);
        isSymbolChar = is_symbol_char(result);
        
        if (!isSymbolChar) break;
        
        result = tokenizer_next_char(tokenizer);
        string_buffer_append_char(tokenizer->buffer, (char)result);
    }

    return 'S';
}

// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_next function gets the next token of the tokenizer by reading the stream sequentially, assigning the token to lasttoken field, and returning it.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer);
    //@ ensures tokenizer(tokenizer);
{
    int c;
    int token;

    string_buffer_clear(tokenizer->buffer);
    tokenizer_skip_whitespace(tokenizer);

    c = tokenizer_peek(tokenizer);

    if (c == '(' || c == ')' || c == -1)
    {
        tokenizer_drop(tokenizer);
        token = c;
    }
    else if (is_digit(c))
    {
        token = tokenizer_eat_number(tokenizer);
    }
    else if (is_symbol_char(c))
    {
        token = tokenizer_eat_symbol(tokenizer);
    }
    else
    {
        tokenizer_drop(tokenizer);
        token = 'B'; // bad character
    }
    tokenizer->lasttoken = token;
    return token;
}