#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// A predicate family to model the state of the character reader.
// A concrete instance would define what it means to be ready to read.
predicate_family charreader_pre(void* reader)();

// The charreader function type. It is specified to return an integer
// representing a character or EOF, within a specific range.
typedef int charreader();
    //@ requires charreader_pre(this)();
    //@ ensures -128 <= result && result <= 127;

struct tokenizer;

// A helper predicate to group the invariant fields of the tokenizer.
predicate tokenizer_fields(struct tokenizer *t; charreader *reader, int lasttoken, struct string_buffer *buffer) =
    t->next_char |-> reader &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    malloc_block_tokenizer(t) &*&
    string_buffer(buffer, _) &*&
    is_charreader(reader) == true;

// The main predicate for the tokenizer.
// @param is_filled: A boolean indicating if 'lastread' contains a valid character.
// @param lastread_val: The logical value of the 'lastread' field.
predicate tokenizer(struct tokenizer *t; bool is_filled, int lastread_val) =
    t->lastread |-> lastread_val &*&
    tokenizer_fields(t, ?reader, _, _) &*&
    (is_filled ?
        // If filled, lastread must be a valid character.
        -128 <= lastread_val && lastread_val <= 127
    :
        // If not filled, lastread must be -2, and we must hold the precondition for the reader.
        lastread_val == -2 &*& charreader_pre(reader)()
    );
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
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();


/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?is_filled, ?lastread_val);
    //@ ensures tokenizer(tokenizer, true, ?new_lastread_val);
{
    //@ open tokenizer(tokenizer, is_filled, lastread_val);
    //@ open tokenizer_fields(tokenizer, ?reader, ?lasttoken, ?buffer);
	if ( tokenizer->lastread == -2 )
	{
	        //@ assert !is_filled;
	        charreader *reader = tokenizer->next_char;
	        //@ assert charreader_pre(reader)();
	        int result = reader();
			if (result < -128 || result > 127)
				abort(); // This branch is unreachable due to the charreader's contract.
		tokenizer->lastread = result;
	} else {
	    //@ assert is_filled;
	}
	//@ int new_lastread_val = tokenizer->lastread;
	//@ close tokenizer_fields(tokenizer, reader, lasttoken, buffer);
	//@ close tokenizer(tokenizer, true, new_lastread_val);
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?is_filled, ?lastread_val);
    //@ ensures tokenizer(tokenizer, true, result);
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, true, ?new_lastread_val);
	int result = tokenizer->lastread;
	//@ assert result == new_lastread_val;
	//@ close tokenizer(tokenizer, true, new_lastread_val);
	return result;
}