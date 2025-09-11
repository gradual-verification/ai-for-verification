#include "stdio.h"
#include "stdlib.hh"
#include "stringBuffers.h"

/*@
// --- Predicate for charreader ---

predicate_family charreader_state(charreader* reader)(list<int> s);

// --- Predicate for tokenizer ---

predicate tokenizer(struct tokenizer *t; list<char> buffer_content, list<int> stream) =
    t->next_char |-> ?reader &*& is_charreader(reader) == true &*&
    t->lastread |-> ?lastread &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?sb &*&
    string_buffer(sb, buffer_content) &*&
    (
        lastread == -2 ?
            charreader_state(reader)(stream)
        :
            stream == nil ?
                lastread == -1 &*& charreader_state(reader)(nil)
            :
                lastread == head(stream) &*& charreader_state(reader)(tail(stream))
    );

// --- Helper fixpoints and lemmas for tokenizer_eat_number ---

fixpoint bool is_digit_int(int c) { return c >= '0' && c <= '9'; }

fixpoint list<char> digit_prefix(list<int> s) {
    switch(s) {
        case nil: return nil;
        case cons(h, t):
            return is_digit_int(h) ? cons((char)h, digit_prefix(t)) : nil;
    }
}

fixpoint list<int> digit_prefix_int(list<int> s) {
    switch(s) {
        case nil: return nil;
        case cons(h, t):
            return is_digit_int(h) ? cons(h, digit_prefix_int(t)) : nil;
    }
}

fixpoint list<int> drop_digit_prefix(list<int> s) {
    switch(s) {
        case nil: return nil;
        case cons(h, t):
            return is_digit_int(h) ? drop_digit_prefix(t) : s;
    }
}

lemma void length_digit_prefix(list<int> s)
    requires true;
    ensures length(digit_prefix(s)) == length(digit_prefix_int(s));
{
    switch(s) {
        case nil:
        case cons(h, t):
            if (is_digit_int(h)) {
                length_digit_prefix(t);
            }
    }
}

lemma void drop_digit_prefix_def(list<int> s)
    requires true;
    ensures drop_digit_prefix(s) == drop(length(digit_prefix_int(s)), s);
{
    switch(s) {
        case nil:
        case cons(h, t):
            if (is_digit_int(h)) {
                length_digit_prefix(t);
                drop_digit_prefix_def(t);
            }
    }
}

@*/

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires charreader_state(this)(?s);
    //@ ensures s == nil ? charreader_state(this)(nil) &*& result == -1 : charreader_state(this)(tail(s)) &*& result == head(s);


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
//@ requires tokenizer(tokenizer, ?bcs, ?stream);
//@ ensures tokenizer(tokenizer, bcs, stream);
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
{
    //@ open tokenizer(tokenizer, bcs, stream);
	if ( tokenizer->lastread == -2 )
	{
	        //@ open charreader_state(tokenizer->next_char)(stream);
	        charreader *reader = tokenizer->next_char;
	        int result = reader();
			if (result < -128 || result > 127)
				abort();
		tokenizer->lastread = result;
		//@ if (stream == nil) { assert result == -1; } else { assert result == head(stream); }
	}
	//@ close tokenizer(tokenizer, bcs, stream);
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(tokenizer, ?bcs, ?stream);
//@ ensures tokenizer(tokenizer, bcs, stream) &*& result == (stream == nil ? -1 : head(stream));
int tokenizer_peek(struct tokenizer* tokenizer)
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, bcs, stream);
	//@ close tokenizer(tokenizer, bcs, stream);
	return tokenizer->lastread;
}


/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(tokenizer, ?bcs, ?stream);
//@ ensures stream == nil ? tokenizer(tokenizer, bcs, nil) &*& result == -1 : tokenizer(tokenizer, bcs, tail(stream)) &*& result == head(stream);
int tokenizer_next_char(struct tokenizer* tokenizer)
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, bcs, stream);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ list<int> new_stream = stream == nil ? nil : tail(stream);
	//@ close tokenizer(tokenizer, bcs, new_stream);
	return c;
}


/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.

It ensures nothing.
*/
//@ requires true;
//@ ensures result == (c >= '0' && c <= '9');
bool is_digit(int c)
{
	return c >= '0' && c <= '9';
}


/***
 * Description:
The string_buffer_append_char function appends a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
//@ requires string_buffer(buffer, ?bcs);
//@ ensures string_buffer(buffer, append(bcs, cons(c, nil)));
void string_buffer_append_char(struct string_buffer *buffer, char c)
{
	char cc = c;
	string_buffer_append_chars(buffer, &cc, 1);
}


// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_eat_number function reads all the digit characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and returns the token that represents digit.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(tokenizer, ?bcs0, ?stream0);
//@ ensures tokenizer(tokenizer, append(bcs0, digit_prefix(stream0)), drop_digit_prefix(stream0)) &*& result == '0';
int tokenizer_eat_number(struct tokenizer* tokenizer)
{
	for (;;)
	    /*@
	    invariant
	        tokenizer(tokenizer, ?bcs, ?stream) &*&
	        append(bcs0, digit_prefix(stream0)) == append(bcs, digit_prefix(stream)) &*&
	        stream == drop(length(bcs) - length(bcs0), stream0);
	    @*/
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);
		//@ assert tokenizer(tokenizer, bcs, stream);
		//@ if (stream == nil) { assert result == -1; } else { assert result == head(stream); }
		
		isDigit = is_digit(result);
		//@ if (stream == nil) { assert isDigit == false; } else { assert isDigit == is_digit_int(head(stream)); }
		
		if ( !isDigit ) break;
		
		//@ assert stream != nil && is_digit_int(head(stream));
		
	    result = tokenizer_next_char(tokenizer);
	    //@ assert tokenizer(tokenizer, bcs, tail(stream)) &*& result == head(stream);
	    
	    //@ open tokenizer(tokenizer, bcs, tail(stream));
		string_buffer_append_char(tokenizer->buffer, (char)result);
		//@ list<char> new_bcs = append(bcs, cons((char)result, nil));
		//@ list<int> new_stream = tail(stream);
		//@ close tokenizer(tokenizer, new_bcs, new_stream);
		
		/*@
		// Prove invariant part 1: append(bcs0, digit_prefix(stream0)) == append(new_bcs, digit_prefix(new_stream))
		append_assoc(bcs, cons((char)result, nil), digit_prefix(tail(stream)));
		
		// Prove invariant part 2: new_stream == drop(length(new_bcs) - length(bcs0), stream0)
		length_append(bcs, cons((char)result, nil));
		drop_n_plus_one(length(bcs) - length(bcs0), stream0);
		@*/
	}

	/*@
	assert tokenizer(tokenizer, ?bcs, ?stream);
	if (stream == nil) {
	    assert digit_prefix(stream) == nil;
	} else {
	    assert !is_digit_int(head(stream));
	    assert digit_prefix(stream) == nil;
	}
	append_nil(bcs);
	length_digit_prefix(stream0);
	drop_digit_prefix_def(stream0);
	@*/

	return '0';
}