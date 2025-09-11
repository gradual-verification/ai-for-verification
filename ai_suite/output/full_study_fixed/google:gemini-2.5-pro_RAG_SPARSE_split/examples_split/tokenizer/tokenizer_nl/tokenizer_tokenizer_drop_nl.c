#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
/*@
// An abstract predicate representing the state of the input source for a charreader.
// A real implementation would make this concrete, e.g. by wrapping a file or a string.
predicate char_source();

// A contract for the charreader function pointer type.
// This makes VeriFast define the 'is_charreader' predicate.
typedef int charreader();
    requires char_source();
    ensures char_source() &*& result >= -1; // EOF is -1
@*/
typedef int charreader();


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
// A predicate representing a tokenizer object.
// It owns the memory for the struct and its fields.
// It does not own the char_source, as that belongs to the charreader implementation.
// The predicate is precise: the values of the fields are uniquely determined by the address of the tokenizer struct.
predicate tokenizer(struct tokenizer *t; charreader *nc, int lr, int lt, struct string_buffer *buf, list<char> cs) =
    t->next_char |-> nc &*& is_charreader(nc) == true &*&
    t->lastread |-> lr &*&
    t->lasttoken |-> lt &*&
    t->buffer |-> buf &*&
    string_buffer(buf, cs);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?nc, ?lr, ?lt, ?buf, ?cs);
//@ ensures tokenizer(tokenizer, nc, -2, lt, buf, cs);
{
	//@ open tokenizer(tokenizer, nc, lr, lt, buf, cs);
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, nc, -2, lt, buf, cs);
}