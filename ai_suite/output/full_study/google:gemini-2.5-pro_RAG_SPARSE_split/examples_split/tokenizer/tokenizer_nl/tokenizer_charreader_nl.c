#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// A predicate family for the precondition of a charreader.
// The first argument is the function pointer of the charreader.
// The second argument, 'info', is a ghost parameter that can carry
// any information about the state of the charreader.
predicate_family charreader_pre(void* func_ptr)(any info);

// A predicate family for the postcondition of a charreader.
// It relates the pre-state 'info' to the post-state and the character read.
predicate_family charreader_post(void* func_ptr)(any info, int char_read);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires charreader_pre(this)(?info);
    //@ ensures charreader_post(this)(info, result) &*& (result == -1 || (0 <= result && result <= 255));

/*@
// A predicate representing a tokenizer.
// The ghost parameters track the logical state of the tokenizer.
predicate tokenizer(struct tokenizer *t; any charreader_info, int lastread, int lasttoken, list<char> cs) =
    t->next_char |-> ?f &*& is_charreader(f) == true &*&
    t->lastread |-> lastread &*& (-2 <= lastread && lastread <= 255) &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> ?sb &*& string_buffer(sb, cs) &*&
    charreader_pre(f)(charreader_info);
@*/

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};