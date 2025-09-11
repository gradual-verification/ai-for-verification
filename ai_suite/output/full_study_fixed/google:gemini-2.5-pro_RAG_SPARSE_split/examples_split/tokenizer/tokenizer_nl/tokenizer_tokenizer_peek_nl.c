#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// predicate families for charreader
predicate_family_pre(charreader_pre, charreader*, any)
predicate_family_post(charreader_post, charreader*, any, int)

// abstract specification of a charreader
predicate charreader_pre(charreader* reader; any info);
predicate charreader_post(charreader* reader; any info, int result);
@*/

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
//@ requires [?f]charreader_pre(this, ?info);
//@ ensures [f]charreader_post(this, info, result) &*& result >= -128 &*& result <= 127;


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer *t; int lastread, int lasttoken, list<char> cs, any reader_info) =
    t->next_char |-> ?reader &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> ?b &*&
    malloc_block_tokenizer(t) &*&
    is_charreader(reader) == true &*&
    string_buffer(b, cs) &*&
    lastread >= -2 &*& lastread <= 127 &*&
    (lastread == -2 ?
        charreader_pre(reader, reader_info)
    :
        charreader_post(reader, reader_info, lastread)
    );
@*/


/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?lr, ?lt, ?cs, ?info);
//@ ensures tokenizer(tokenizer, ?new_lr, lt, cs, info) &*& (lr == -2 ? new_lr != -2 : new_lr == lr);
{
    //@ open tokenizer(tokenizer, lr, lt, cs, info);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		    tokenizer->lastread = result;
            //@ close tokenizer(tokenizer, result, lt, cs, info);
	} else {
        //@ close tokenizer(tokenizer, lr, lt, cs, info);
    }
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
//@ requires tokenizer(tokenizer, ?lr, ?lt, ?cs, ?info);
//@ ensures tokenizer(tokenizer, result, lt, cs, info) &*& (lr == -2 ? result != -2 : result == lr);
{
	tokenizer_fill_buffer(tokenizer);
	return tokenizer->lastread;
}