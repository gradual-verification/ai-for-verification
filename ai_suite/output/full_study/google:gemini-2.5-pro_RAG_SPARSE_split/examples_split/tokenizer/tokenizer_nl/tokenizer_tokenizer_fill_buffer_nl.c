#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"


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
/*@
// An abstract model of a character source. It's a list of integers.
predicate char_source(void *reader; list<int> cs);
@*/

typedef int charreader();
    //@ requires char_source(this, ?cs);
    /*@ ensures
            cs == nil ?
                result == -1 &*& char_source(this, nil)
            :
                result == head(cs) &*& char_source(this, tail(cs));
    @*/

/*@
// A helper fixpoint to check if an integer is within the signed char range.
fixpoint bool signed_char_range(int c) { return -128 <= c && c <= 127; }

// The predicate representing a valid tokenizer.
// It owns the tokenizer struct fields and the associated character source.
predicate tokenizer(struct tokenizer *t; list<int> source_cs, int lastread, int lasttoken, list<char> buffer_cs) =
    t->next_char |-> ?reader &*&
    char_source(reader, source_cs) &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> ?sb &*&
    string_buffer(sb, buffer_cs) &*&
    malloc_block_tokenizer(t);
@*/


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?source_cs, ?lastread, ?lasttoken, ?buffer_cs) &*& forall(source_cs, (signed_char_range));
    /*@ ensures
            lastread != -2 ?
                tokenizer(tokenizer, source_cs, lastread, lasttoken, buffer_cs)
            :
                source_cs == nil ?
                    tokenizer(tokenizer, nil, -1, lasttoken, buffer_cs)
                :
                    tokenizer(tokenizer, tail(source_cs), head(source_cs), lasttoken, buffer_cs);
    @*/
{
	//@ open tokenizer(tokenizer, source_cs, lastread, lasttoken, buffer_cs);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
			
			//@ switch(source_cs) { case nil: {} case cons(h,t): { forall_elim(source_cs, (signed_char_range), h); } }
			
			if (result < -128 || result > 127)
				abort();
				
		    tokenizer->lastread = result;
		    
		    /*@
		    if (source_cs == nil) {
		        assert result == -1;
		        close tokenizer(tokenizer, nil, -1, lasttoken, buffer_cs);
		    } else {
		        assert result == head(source_cs);
		        close tokenizer(tokenizer, tail(source_cs), head(source_cs), lasttoken, buffer_cs);
		    }
		    @*/
	}
	else
	{
	    //@ close tokenizer(tokenizer, source_cs, lastread, lasttoken, buffer_cs);
	}
}