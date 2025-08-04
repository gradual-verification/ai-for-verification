#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@

// Predicate for the abstract state of a character reader
predicate charreader_state(charreader* reader; list<int> stream);

// Predicate for the tokenizer struct
predicate tokenizer(struct tokenizer *t; list<char> consumed_by_buffer, list<int> stream) =
    t->next_char |-> ?reader &*& is_charreader(reader) == true &*&
    t->lastread |-> ?lastread &*&
    t->lasttoken |-> ?lasttoken &*&
    t->buffer |-> ?buffer &*&
    malloc_block_tokenizer(t) &*&
    string_buffer(buffer, consumed_by_buffer) &*&
    charreader_state(reader, ?reader_stream) &*&
    (lastread == -2 ? // buffer empty
        stream == reader_stream
    : lastread == -1 ? // EOF
        stream == nil &*& reader_stream == nil
    : // char in buffer
        -128 <= lastread &*& lastread <= 127 &*&
        stream == cons(lastread, reader_stream)
    );

// Specification for is_symbol_char
fixpoint bool is_symbol_char_spec(int c) {
    return c > 32 && c <= 127 && c != '(' && c != ')';
}

// Helper fixpoints for the main function's spec
fixpoint list<int> take_while_int(fixpoint(int, bool) p, list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return p(h) ? cons(h, take_while_int(p, t)) : nil;
    }
}

fixpoint list<int> drop_while_int(fixpoint(int, bool) p, list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return p(h) ? drop_while_int(p, t) : xs;
    }
}

fixpoint list<char> ints_to_chars(list<int> xs) {
    switch(xs) {
        case nil: return nil;
        case cons(h, t): return cons((char)h, ints_to_chars(t));
    }
}

// Helper lemmas for proving the main function

lemma void forall_append<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
    requires forall(xs, p) &*& forall(ys, p);
    ensures forall(append(xs, ys), p);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            forall_append(t, ys, p);
    }
}

lemma void ints_to_chars_append(list<int> l1, list<int> l2)
    requires true;
    ensures ints_to_chars(append(l1, l2)) == append(ints_to_chars(l1), ints_to_chars(l2));
{
    switch(l1) {
        case nil:
        case cons(h, t):
            ints_to_chars_append(t, l2);
    }
}

lemma void append_take_while_drop_while_int(fixpoint(int, bool) p, list<int> xs)
    requires true;
    ensures append(take_while_int(p, xs), drop_while_int(p, xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (p(h)) {
                append_take_while_drop_while_int(p, t);
            }
    }
}

// This is the key lemma for the loop termination case.
lemma void take_while_properties_int(fixpoint(int, bool) p, list<int> consumed, list<int> stream)
    requires forall(consumed, p) == true &*& (stream == nil || !p(head(stream)));
    ensures take_while_int(p, append(consumed, stream)) == consumed &*&
            drop_while_int(p, append(consumed, stream)) == stream;
{
    switch (consumed) {
        case nil:
        case cons(h, t):
            open forall(consumed, p);
            take_while_properties_int(p, t, stream);
    }
}

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
    //@ requires charreader_state(this, ?s);
    /*@ ensures s == nil ?
                    result == -1 &*& charreader_state(this, nil)
                :
                    -128 <= head(s) &*& head(s) <= 127 &*&
                    result == head(s) &*& charreader_state(this, tail(s));
    @*/


/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?consumed, ?stream);
    //@ ensures tokenizer(tokenizer, consumed, stream);
{
    //@ open tokenizer(tokenizer, consumed, stream);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        //@ open charreader_state(reader, stream);
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
		//@ if (stream == nil) { assert result == -1; } else { assert result == head(stream); }
	}
	//@ close tokenizer(tokenizer, consumed, stream);
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?consumed, ?stream);
    //@ ensures tokenizer(tokenizer, consumed, stream) &*& result == (stream == nil ? -1 : head(stream));
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, consumed, stream);
	//@ if (stream == nil) { assert tokenizer->lastread == -1; } else { assert tokenizer->lastread == head(stream); }
	int c = tokenizer->lastread;
	//@ close tokenizer(tokenizer, consumed, stream);
	return c;
}


/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?consumed, ?stream);
    /*@ ensures stream == nil ?
                  tokenizer(tokenizer, consumed, nil) &*& result == -1
              :
                  tokenizer(tokenizer, consumed, tail(stream)) &*& result == head(stream);
    @*/
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, consumed, stream);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ if (stream == nil) { assert c == -1; } else { assert c == head(stream); }
	//@ close tokenizer(tokenizer, consumed, tail(stream));
	return c;
}


/***
 * Description:
The string_buffer_append_char function appends a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void string_buffer_append_char(struct string_buffer *buffer, char c)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, append(cs, cons(c, nil)));
{
	char cc = c;
	//@ character_to_chars(&cc);
	string_buffer_append_chars(buffer, &cc, 1);
	//@ chars_to_character(&cc);
}


/***
 * Description:
The is_symbol_char function checks whether a given character in integer means a symbol in ASCII (except parentheses).

It ensures nothing
*/
bool is_symbol_char(int c)
    //@ requires true;
    //@ ensures result == is_symbol_char_spec(c);
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_eat_symbol function reads all the ASCII symbol characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-symbol character, it exits the loop and return the token that represents symbol.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_eat_symbol(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?consumed, ?stream);
    /*@ ensures tokenizer(tokenizer,
                         append(consumed, ints_to_chars(take_while_int(is_symbol_char_spec, stream))),
                         drop_while_int(is_symbol_char_spec, stream)) &*&
                result == 'S';
    @*/
{
    //@ list<int> eaten_symbols = nil;
	for (;;)
        /*@
        invariant tokenizer(tokenizer, append(consumed, ints_to_chars(eaten_symbols)), ?current_stream) &*&
                  append(eaten_symbols, current_stream) == stream &*&
                  forall(eaten_symbols, (is_symbol_char_spec));
        @*/
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		//@ assert result == (current_stream == nil ? -1 : head(current_stream));
		isSymbolChar = is_symbol_char(result);
		//@ assert isSymbolChar == is_symbol_char_spec(result);
		
		if (!isSymbolChar) {
		    //@ append_take_while_drop_while_int(is_symbol_char_spec, stream);
		    //@ take_while_properties_int(is_symbol_char_spec, eaten_symbols, current_stream);
		    break;
		}
		
		//@ list<int> old_eaten_symbols = eaten_symbols;
		//@ list<char> old_consumed = append(consumed, ints_to_chars(eaten_symbols));
		result = tokenizer_next_char(tokenizer);
		//@ assert result == head(current_stream);
		//@ assert tokenizer(tokenizer, old_consumed, tail(current_stream));
		
		//@ open tokenizer(tokenizer, old_consumed, tail(current_stream));
		string_buffer_append_char(tokenizer->buffer, (char)result);
		
		//@ eaten_symbols = append(eaten_symbols, cons(result, nil));
		//@ ints_to_chars_append(old_eaten_symbols, cons(result, nil));
		//@ append_assoc(consumed, ints_to_chars(old_eaten_symbols), cons((char)result, nil));
		//@ assert string_buffer(tokenizer->buffer, append(consumed, ints_to_chars(eaten_symbols)));
		
		//@ append_assoc(old_eaten_symbols, cons(result, nil), tail(current_stream));
		
		//@ forall_append(old_eaten_symbols, cons(result, nil), is_symbol_char_spec);
		
		//@ close tokenizer(tokenizer, append(consumed, ints_to_chars(eaten_symbols)), tail(current_stream));
	}

	return 'S';
}