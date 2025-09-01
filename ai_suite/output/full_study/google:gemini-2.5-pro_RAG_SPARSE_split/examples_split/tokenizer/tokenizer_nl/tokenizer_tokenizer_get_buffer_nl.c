#include "stdio.h"
#include "stdlib.hh"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
//@ predicate is_charreader(charreader *f);


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
// Predicate for the core data of a tokenizer, without owning the string_buffer's content.
// It is parameterized by the buffer pointer `sb` to link it to the string_buffer predicate.
predicate tokenizer_core(struct tokenizer *tok; struct string_buffer *sb) =
    tok->next_char |-> ?f &*& is_charreader(f) == true &*&
    tok->lastread |-> _ &*&
    tok->lasttoken |-> _ &*&
    tok->buffer |-> sb &*&
    malloc_block_tokenizer(tok);

// Predicate for a fully-owned tokenizer, including its string buffer.
predicate tokenizer(struct tokenizer *tok; list<char> cs) =
    exists(?sb) &*&
    tokenizer_core(tok, sb) &*&
    string_buffer(sb, cs);

// Lemma to re-assemble a tokenizer from its parts.
lemma void tokenizer_unsplit(struct tokenizer *tok);
    requires tokenizer_core(tok, ?sb) &*& string_buffer(sb, ?cs);
    ensures tokenizer(tok, cs);
{
    close exists(sb);
    close tokenizer(tok, cs);
}
@*/


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_get_buffer function returns the buffer of a given tokenizer

It needs to make sure that the given tokenizer preserves its property of tokenizer, and 
the return value is a string buffer.
*/
struct string_buffer *tokenizer_get_buffer(struct tokenizer *tokenizer)
    //@ requires tokenizer(tokenizer, ?cs);
    //@ ensures tokenizer_core(tokenizer, result) &*& string_buffer(result, cs);
{
    //@ open tokenizer(tokenizer, cs);
    //@ open exists(?sb);
    //@ open tokenizer_core(tokenizer, sb);
    struct string_buffer *b = tokenizer->buffer;
    //@ close tokenizer_core(tokenizer, b);
    return b;
}