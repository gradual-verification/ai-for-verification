#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
//@ requires token(?t1) &*& read_char_io(t1, stdin, ?c, ?success, ?t2);
//@ ensures token(t2) &*& result == c;


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer* t; charreader* reader, int lastread, int lasttoken, struct string_buffer* buffer) =
    t->next_char |-> reader &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> lasttoken &*&
    t->buffer |-> buffer &*&
    is_charreader(reader) == true &*&
    string_buffer(buffer, _);
@*/

// TODO: make this function pass the verification
int getchar() //@ : charreader
//@ requires token(?t1) &*& read_char_io(t1, stdin, ?c, ?success, ?t2);
//@ ensures token(t2) &*& result == c;
{
    int c;
    c = getc(stdin);
    return c;
}