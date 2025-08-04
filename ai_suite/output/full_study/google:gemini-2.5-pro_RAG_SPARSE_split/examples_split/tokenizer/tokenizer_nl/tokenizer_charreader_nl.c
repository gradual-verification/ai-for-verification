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
// A predicate family to represent the abstract state of a charreader.
// The state is modeled as a list of characters to be read.
// An implementation of a charreader will provide an instance of this
// predicate family to hold the state it needs, e.g., a file handle.
predicate_family charreader_state(void *reader)(list<char> cs);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    /*@ requires
            // The caller must provide the state of the charreader.
            // 'this' refers to the function pointer being called.
            charreader_state(this, ?cs);
    @*/
    /*@ ensures
            cs == nil ?
                // If the stream is empty, it's End-Of-File. The state remains empty.
                // The return value is -1, which corresponds to EOF.
                charreader_state(this, nil) &*& result == -1
            :
                // Otherwise, consume one character from the head of the list...
                charreader_state(this, tail(cs)) &*&
                // ...and return it. The character is returned as an unsigned value
                // in an int, similar to standard functions like fgetc.
                result == (unsigned char)head(cs);
    @*/
