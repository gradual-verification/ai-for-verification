#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

struct tokenizer
{
    charreader*           next_char;
    int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
    int                   lasttoken; // the last token parsed
    struct string_buffer* buffer;
};

/***
 * Description:
The print_string_buffer function prints the content in a string buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void print_string_buffer(struct string_buffer *buffer)
    //@ requires [?f]string_buffer(buffer, ?cs);
    //@ ensures [f]string_buffer(buffer, cs);
{
    int n = string_buffer_get_length(buffer);
    char *pcs = string_buffer_get_chars(buffer);
    int i;
    for (i = 0; i < n; i++)
    {
        putchar(pcs[i]);
    }
    //@ string_buffer_merge_chars(buffer);
}

// TODO: make this function pass the verification
/***
 * Description:
The print_token function prints the last token of a tokenizer by reading its lasttoken field and prints a readable content of the token.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void print_token(struct tokenizer* tokenizer)
    //@ requires [?f]tokenizer->buffer |-> ?buffer &*& [f]string_buffer(buffer, ?bcs) &*& integer(&tokenizer->lasttoken, ?lasttoken);
    //@ ensures [f]tokenizer->buffer |-> buffer &*& [f]string_buffer(buffer, bcs) &*& integer(&tokenizer->lasttoken, lasttoken);
{
    switch (tokenizer->lasttoken)
    {
    case '(':
        puts("LPAREN");
        break;

    case ')':
        puts("RPAREN");
        break;

    case '0':
        putchar('N');
        print_string_buffer(tokenizer->buffer);
        puts("");
        break;

    case 'S':
        putchar('S');
        print_string_buffer(tokenizer->buffer);
        puts("");
        break;
    
    case 'B':
        puts("BADCHAR");
        break;
    }
}