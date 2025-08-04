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

/*@
// We introduce a predicate family to hold the permission to call a charreader.
// This ensures that the charreader is not called concurrently by multiple threads,
// which is crucial for resource safety with I/O operations.
predicate_family charreader_contract(void* reader)();

predicate Tokenizer(struct tokenizer* t;) =
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*& charreader_contract(nc)() &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> ?b &*& string_buffer(b, _);

predicate Tokenizer_minus_buffer(struct tokenizer* t; struct string_buffer *buffer) =
  t->next_char |-> ?nc &*& is_charreader(nc) == true &*& charreader_contract(nc)() &*&
  t->lastread |-> ?lastread &*&
  t->lasttoken |-> ?lasttoken &*&
  t->buffer |-> buffer;
@*/


typedef int charreader();
    //@ requires charreader_contract(this)();
    /*@ ensures charreader_contract(this)() &*&
                // The implementation of tokenizer_fill_buffer contains a check that aborts
                // if the result is outside the range of a signed 8-bit integer.
                // We strengthen the contract to reflect this assumption.
                result >= -128 && result <= 127;
    @*/


// TODO: make this function pass the verification
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
 //@ requires Tokenizer(tokenizer);
 //@ ensures Tokenizer(tokenizer);
{
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
}