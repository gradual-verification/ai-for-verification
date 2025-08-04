#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// A predicate family to identify charreader function pointers.
predicate_family is_charreader(void* f)();
@*/

// Forward declaration for the typedef used in the struct
typedef int charreader();

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
// A predicate describing a valid tokenizer struct.
// It owns the memory for the struct and its fields, including the associated string_buffer.
predicate tokenizer(struct tokenizer *t; charreader *next_char, int lastread, int lasttoken, struct string_buffer *buffer, list<char> cs) =
    t->next_char |-> next_char &*&
    is_charreader(next_char) == true &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    string_buffer(buffer, cs);
@*/


/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires is_charreader(this)();
    //@ ensures true; // The implementation details are not important for the tokenizer_drop function.


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?nc, ?lr, ?lt, ?b, ?cs);
    //@ ensures tokenizer(tokenizer, nc, -2, lt, b, cs);
{
	//@ open tokenizer(tokenizer, nc, lr, lt, b, cs);
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, nc, -2, lt, b, cs);
}