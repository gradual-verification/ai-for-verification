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
typedef int charreader();

/*@
// A charreader is a function that returns the next character from a stream.
// It returns -1 on end-of-file.
// We model the stream of characters as a ghost list of chars.

predicate charreader_state(charreader* f; list<char> stream);

// The contract for a charreader function pointer.
typedef lemma void is_charreader(charreader* f);
    requires [?q]charreader_state(f, ?s);
    ensures
        s == nil ?
            ([q]charreader_state(f, nil) &*& result == -1)
        :
            ([q]charreader_state(f, tail(s)) &*& result == head(s) &*& -128 <= head(s) &*& head(s) <= 127);

// The state of a tokenizer. It is parameterized by the remaining stream of characters.
// We use tokenizer_p to avoid a name clash with the struct.
predicate tokenizer_p(struct tokenizer *t; list<char> stream) =
    t->next_char |-> ?reader
    &*& t->lastread |-> ?lastread
    &*& t->lasttoken |-> _
    &*& t->buffer |-> ?buffer
    &*& [1/2]is_charreader(reader)
    &*& [1/2]charreader_state(reader, ?reader_stream)
    &*& string_buffer(buffer, _)
    &*& lastread == -2 ? // buffer is empty, stream is what the reader will produce
        stream == reader_stream
    : lastread == -1 ? // EOF reached, stream is empty
        stream == nil &*& reader_stream == nil
    : // character in buffer, stream is that char plus what the reader will produce
        -128 <= lastread &*& lastread <= 127 &*&
        stream == cons(lastread, reader_stream);
@*/


/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer_p(tokenizer, ?s);
    //@ ensures tokenizer_p(tokenizer, s);
{
    //@ open tokenizer_p(tokenizer, s);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        //@ is_charreader *is_reader = reader;
	        //@ is_reader();
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
    //@ close tokenizer_p(tokenizer, s);
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer_p(tokenizer, ?s);
    //@ ensures s == nil ? (tokenizer_p(tokenizer, nil) &*& result == -1) : (tokenizer_p(tokenizer, tail(s)) &*& result == head(s));
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer_p(tokenizer, s);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ assert tokenizer->next_char |-> ?reader &*& [1/2]charreader_state(reader, ?reader_stream);
	//@ close tokenizer_p(tokenizer, reader_stream);
	return c;
}