#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();

/*@
fixpoint bool is_valid_read_char(int c) {
    return c >= -128 && c <= 127;
}

// An abstract charreader that produces a stream of integers.
predicate is_charreader(charreader* f; list<int> stream);

// Contract for calling a charreader.
typedef int charreader_contract();
    requires is_charreader(this, ?s);
    ensures
        s == nil ?
            is_charreader(this, nil) &*& result == -1
        :
            is_charreader(this, tail(s)) &*& result == head(s) &*&
            (head(s) == -1 || is_valid_read_char(head(s)) == true);

// The state of a tokenizer. It is parameterized by the remaining input stream
// (until EOF) and the current content of its internal string_buffer.
predicate tokenizer(struct tokenizer *t; list<int> stream, list<char> buffer_cs) =
    t->next_char |-> ?reader &*&
    is_charreader_contract(reader) == true &*&
    t->lastread |-> ?lastread &*&
    t->lasttoken |-> ?lasttoken &*&
    t->buffer |-> ?buffer &*&
    malloc_block_tokenizer(t) &*&
    is_charreader(reader, ?reader_stream) &*&
    string_buffer(buffer, buffer_cs) &*&
    (
        lastread == -2 ? // Buffer is empty
            append(stream, cons(-1, nil)) == reader_stream
        : // A character or EOF is buffered
            append(stream, cons(-1, nil)) == cons(lastread, reader_stream)
    ) &*&
    forall(stream, (is_valid_read_char));

fixpoint list<t> take_while<t>(fixpoint(t, bool) p, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return p(h) ? cons(h, take_while(p, t)) : nil;
    }
}

fixpoint list<char> chars_of_ints(list<int> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return cons((char)h, chars_of_ints(t));
    }
}

lemma void chars_of_ints_append(list<int> xs, list<int> ys)
    requires true;
    ensures chars_of_ints(append(xs, ys)) == append(chars_of_ints(xs), chars_of_ints(ys));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            chars_of_ints_append(t, ys);
    }
}

lemma void take_while_append<t>(fixpoint(t, bool) p, list<t> xs, list<t> ys)
    requires forall(xs, p) == true;
    ensures take_while(p, append(xs, ys)) == append(xs, take_while(p, ys));
{
    switch(xs) {
        case nil:
        case cons(h, t):
            forall_elim(xs, p, h);
            take_while_append(p, t, ys);
    }
}

lemma void forall_append_preserves<t>(list<t> xs, list<t> ys, fixpoint(t, bool) p)
    requires forall(xs, p) && forall(ys, p);
    ensures forall(append(xs, ys), p);
{
    switch(xs) {
        case nil:
        case cons(h, t):
            forall_append_preserves(t, ys, p);
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
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, s, bcs);
{
	//@ open tokenizer(tokenizer, s, bcs);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        //@ assume(is_charreader_contract(reader) == true);
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
	}
	//@ close tokenizer(tokenizer, s, bcs);
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, s, bcs) &*& result == (s == nil ? -1 : head(s));
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, s, bcs);
	//@ append_is_nil_iff_both_nil(s, cons(-1, nil));
	int result = tokenizer->lastread;
	//@ close tokenizer(tokenizer, s, bcs);
	return result;
}


/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, s == nil ? nil : tail(s), bcs) &*& result == (s == nil ? -1 : head(s));
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, s, bcs);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, s == nil ? nil : tail(s), bcs);
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
    //@ ensures result == (c > 32 && c <= 127 && c != '(' && c != ')');
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
    //@ requires tokenizer(tokenizer, ?s_initial, ?bcs_initial);
    /*@ ensures
            let eaten_prefix = take_while(is_symbol_char, s_initial) in
            let s_final = drop(length(eaten_prefix), s_initial) in
            let bcs_final = append(bcs_initial, chars_of_ints(eaten_prefix)) in
            tokenizer(tokenizer, s_final, bcs_final) &*&
            result == 'S';
    @*/
{
    //@ list<int> eaten_prefix = nil;
	for (;;)
        /*@
        invariant
            tokenizer(tokenizer, ?s, ?bcs) &*&
            s_initial == append(eaten_prefix, s) &*&
            bcs == append(bcs_initial, chars_of_ints(eaten_prefix)) &*&
            forall(eaten_prefix, is_symbol_char) == true;
        @*/
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
        //@ if (s == nil) { assert result == -1; } else { assert result == head(s); }
		
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) {
            /*@
            if (s == nil) {
                assert result == -1;
                assert is_symbol_char(-1) == false;
                assert take_while(is_symbol_char, s) == nil;
            } else {
                assert result == head(s);
                assert is_symbol_char(head(s)) == false;
                assert take_while(is_symbol_char, s) == nil;
            }
            take_while_append(is_symbol_char, eaten_prefix, s);
            @*/
            break;
        }
		
		//@ assert s != nil;
		//@ assert is_symbol_char(head(s)) == true;
		
		result = tokenizer_next_char(tokenizer);
        //@ open tokenizer(tokenizer, tail(s), bcs);
        
		string_buffer_append_char(tokenizer->buffer, (char)result);
        
        //@ list<int> next_eaten_prefix = append(eaten_prefix, cons(result, nil));
        //@ list<char> next_bcs = append(bcs, cons((char)result, nil));
        
        /*@
        append_assoc(eaten_prefix, cons(result, nil), tail(s));
        
        chars_of_ints_append(eaten_prefix, cons(result, nil));
        append_assoc(bcs_initial, chars_of_ints(eaten_prefix), cons((char)result, nil));
        
        forall_append_preserves(eaten_prefix, cons(result, nil), is_symbol_char);
        @*/
        
        //@ eaten_prefix = next_eaten_prefix;
        
        //@ close tokenizer(tokenizer, tail(s), next_bcs);
	}

	return 'S';
}