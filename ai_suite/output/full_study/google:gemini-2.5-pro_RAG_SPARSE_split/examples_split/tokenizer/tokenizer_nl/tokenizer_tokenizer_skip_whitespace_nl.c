#include "stdio.h"
#include "stdlib.hh"
#include "stringBuffers.h"

/*@
// An abstract predicate representing the state of the character reader.
predicate charreader_inv(charreader* reader;);
@*/

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
/*@
    requires charreader_inv(this);
    // The reader returns a character in the signed char range, or -1 for EOF.
    ensures charreader_inv(this) &*& (result == -1 || (result >= -128 && result <= 127));
@*/

/*@
// A predicate representing a valid tokenizer object.
// It is parameterized by the charreader's invariant and the last read character.
predicate tokenizer(struct tokenizer *t; predicate(charreader*) inv, int lastread) =
    t->next_char |-> ?reader &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?buffer &*&
    string_buffer(buffer, _) &*&
    is_charreader(reader) == true &*&
    inv(reader) &*&
    (lastread == -1 || lastread == -2 || (lastread >= -128 && lastread <= 127));
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
//@ requires tokenizer(tokenizer, ?inv, ?lastread);
//@ ensures tokenizer(tokenizer, inv, ?new_lastread) &*& (lastread == -2 ? new_lastread != -2 : new_lastread == lastread);
{
	//@ open tokenizer(tokenizer, inv, lastread);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        //@ assert inv(reader);
	        int result = reader();
	        //@ assert inv(reader);
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
	//@ close tokenizer(tokenizer, inv, tokenizer->lastread);
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?inv, ?lastread);
//@ ensures tokenizer(tokenizer, inv, ?new_lastread) &*& result == new_lastread &*& result != -2;
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, inv, ?new_lastread);
	int c = tokenizer->lastread;
	//@ close tokenizer(tokenizer, inv, new_lastread);
	return c;
}


/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?inv, _);
//@ ensures tokenizer(tokenizer, inv, -2);
{
	//@ open tokenizer(tokenizer, inv, _);
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, inv, -2);
}


/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.

This function ensures nothing. 
*/
bool is_whitespace(int c)
//@ requires true;
//@ ensures result == (c == ' ' || c == '\n' || c == '\r' || c == '\t');
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_skip_whitespace function reads and drops all the whitespace characters that are encountered sequentially by the tokenizer.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?inv, _);
//@ ensures tokenizer(tokenizer, inv, ?lastread) &*& !is_whitespace(lastread) &*& lastread != -2;
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	//@ invariant tokenizer(tokenizer, ?inv, _);
	{
		tokenizer_drop(tokenizer);
	}
}