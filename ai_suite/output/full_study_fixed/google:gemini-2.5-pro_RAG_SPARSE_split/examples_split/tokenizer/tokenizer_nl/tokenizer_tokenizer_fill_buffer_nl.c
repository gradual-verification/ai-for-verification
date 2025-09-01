#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
/*@
// Predicate families for the pre- and post-conditions of a charreader function.
// This allows different charreader implementations to have different states.
predicate_family charreader_pre(void* f)();
predicate_family charreader_post(void* f)(int result);
@*/
typedef int charreader();
    //@ requires is_charreader(this) == true &*& charreader_pre(this)();
    //@ ensures charreader_post(this)(result) &*& (result == -1 || (-128 <= result && result <= 127));


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer *t; charreader* reader, int lastread, int lasttoken, struct string_buffer* buffer, list<char> cs) =
    t->next_char |-> reader &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    malloc_block(t, sizeof(struct tokenizer)) &*&
    string_buffer(buffer, cs) &*&
    is_charreader(reader) == true;
@*/


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    /*@
    requires
        tokenizer(tokenizer, ?reader, ?lastread, ?lasttoken, ?buffer_ptr, ?cs) &*&
        (lastread == -2 ? charreader_pre(reader)() : true);
    @*/
    /*@
    ensures
        lastread == -2 ?
            tokenizer(tokenizer, reader, ?new_lastread, lasttoken, buffer_ptr, cs) &*&
            charreader_post(reader)(new_lastread)
        :
            tokenizer(tokenizer, reader, lastread, lasttoken, buffer_ptr, cs);
    @*/
{
	//@ open tokenizer(tokenizer, reader, lastread, lasttoken, buffer_ptr, cs);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader_local = tokenizer->next_char;
	        int result = reader_local();
		if (result < -128 || result > 127)
			abort();
		tokenizer->lastread = result;
        	//@ close tokenizer(tokenizer, reader, result, lasttoken, buffer_ptr, cs);
	} else {
        	//@ close tokenizer(tokenizer, reader, lastread, lasttoken, buffer_ptr, cs);
    	}
}