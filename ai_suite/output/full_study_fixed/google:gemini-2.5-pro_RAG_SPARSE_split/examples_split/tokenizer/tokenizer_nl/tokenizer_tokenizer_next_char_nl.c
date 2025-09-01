#include "stdio.h"
#include "stdlib.hh"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
// Abstract specification for a charreader.
// It is a stateful function. The state is represented by the pre/post predicates.
// The `reader` parameter to the predicate family is the function pointer itself,
// which acts as a unique identifier for the reader instance.
predicate_family_instance charreader_pre(void* reader)();
predicate_family_instance charreader_post(void* reader)(int c);

// Predicate for the tokenizer struct.
// It is parameterized by the last read character.
predicate tokenizer(struct tokenizer *t; int lastread) =
    t->next_char |-> ?reader &*&
    is_charreader(reader) == true &*&
    // The contract for the function pointer call.
    (
        requires charreader_pre(reader)();
        // The reader returns a character in the signed char range.
        // EOF (-1) is also included in this range.
        ensures charreader_post(reader)(result) &*& -128 <= result &*& result <= 127;
    ) : is_charreader_contract(reader) &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?sb &*&
    string_buffer(sb, _);
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
    //@ requires tokenizer(tokenizer, -2) &*& charreader_pre(tokenizer->next_char)();
    /*@ ensures
        exists<int>(?c) &*&
        tokenizer(tokenizer, c) &*&
        charreader_post(tokenizer->next_char)(c) &*&
        -128 <= c &*& c <= 127;
    @*/
    //@ requires tokenizer(tokenizer, ?lastread) &*& lastread != -2;
    //@ ensures tokenizer(tokenizer, lastread);
{
	if ( tokenizer->lastread == -2 )
	{
        //@ open tokenizer(tokenizer, -2);
	    charreader *reader = tokenizer->next_char;
	    int result = reader();
        //@ assert charreader_post(reader)(result) &*& -128 <= result &*& result <= 127;
		if (result < -128 || result > 127)
			abort();
		tokenizer->lastread = result;
        //@ close tokenizer(tokenizer, result);
	}
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, -2) &*& charreader_pre(tokenizer->next_char)();
    /*@ ensures
        exists<int>(?c) &*&
        tokenizer(tokenizer, -2) &*&
        charreader_post(tokenizer->next_char)(c) &*&
        result == c &*&
        -128 <= c &*& c <= 127;
    @*/
    //@ requires tokenizer(tokenizer, ?lastread) &*& lastread != -2;
    /*@ ensures
        tokenizer(tokenizer, -2) &*&
        result == lastread;
    @*/
{
	int c;

	tokenizer_fill_buffer(tokenizer);
    //@ open tokenizer(tokenizer, ?current_lastread);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
    //@ close tokenizer(tokenizer, -2);
	return c;
}