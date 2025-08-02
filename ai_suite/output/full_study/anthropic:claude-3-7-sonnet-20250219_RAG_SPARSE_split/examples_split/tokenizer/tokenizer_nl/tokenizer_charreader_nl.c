#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// Define a predicate for the charreader function pointer
predicate charreader_function(charreader *f;) = 
    is_charreader(f) == true;

// Define a predicate for the tokenizer structure
predicate tokenizer(struct tokenizer *t; charreader *next_char, int lastread, int lasttoken, struct string_buffer *buffer) =
    t->next_char |-> next_char &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    charreader_function(next_char) &*&
    string_buffer(buffer, _);
@*/

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};


// TODO: make this function pass the verification
/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader()
/*@ requires true; @*/
/*@ ensures result >= -1 &*& result <= 255; @*/
;