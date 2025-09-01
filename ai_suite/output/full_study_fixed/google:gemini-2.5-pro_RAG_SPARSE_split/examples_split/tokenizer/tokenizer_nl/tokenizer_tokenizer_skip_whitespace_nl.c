#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
/*@
typedef int charreader();
    requires true;
    // A charreader returns either EOF (-1) or a value in the signed char range.
    ensures result == -1 || (-128 <= result && result <= 127);
@*/
typedef int charreader();

struct tokenizer;

/*@
predicate tokenizer(struct tokenizer *t, int lastread) =
    t->next_char |-> ?reader &*& is_charreader(reader) == true &*&
    t->lastread |-> lastread &*& (lastread == -2 || lastread == -1 || (-128 <= lastread && lastread <= 127)) &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?buffer &*& string_buffer(buffer, _);
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
//@ requires tokenizer(tokenizer, ?lr);
//@ ensures tokenizer(tokenizer, ?new_lr) &*& (lr == -2 ? new_lr != -2 : new_lr == lr);
{
	//@ open tokenizer(tokenizer, lr);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        //@ assert is_charreader(reader) == true;
	        int result = reader();
			if (result < -128 || result > 127)
				abort(); // This is unreachable due to the contract of charreader.
		tokenizer->lastread = result;
	}
	//@ close tokenizer(tokenizer, _);
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?lr);
//@ ensures tokenizer(tokenizer, ?new_lr) &*& (lr == -2 ? new_lr != -2 : new_lr == lr) &*& result == new_lr;
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, ?new_lr);
	int result = tokenizer->lastread;
	//@ close tokenizer(tokenizer, new_lr);
	return result;
}


/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, _);
//@ ensures tokenizer(tokenizer, -2);
{
	//@ open tokenizer(tokenizer, _);
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, -2);
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
//@ requires tokenizer(tokenizer, _);
//@ ensures tokenizer(tokenizer, ?lr) &*& lr != -2 &*& !is_whitespace(lr);
{
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	//@ invariant tokenizer(tokenizer, _);
	{
		tokenizer_drop(tokenizer);
	}
}