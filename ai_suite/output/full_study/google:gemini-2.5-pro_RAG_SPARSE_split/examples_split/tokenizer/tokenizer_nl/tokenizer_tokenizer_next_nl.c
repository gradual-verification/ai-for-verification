#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
fixpoint bool is_whitespace(int c) {
    return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}

fixpoint bool is_digit(int c) {
    return c >= '0' && c <= '9';
}

fixpoint bool is_symbol_char(int c) {
    return c > 32 && c <= 127 && c != '(' && c != ')';
}

fixpoint bool is_whitespace_char(char c) { return is_whitespace((int)c); }
fixpoint bool is_digit_char(char c) { return is_digit((int)c); }
fixpoint bool is_symbol_char_char(char c) { return is_symbol_char((int)c); }

fixpoint list<char> take_while(fixpoint(char, bool) p, list<char> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return p(h) ? cons(h, take_while(p, t)) : nil;
    }
}

fixpoint list<char> drop_while(fixpoint(char, bool) p, list<char> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return p(h) ? drop_while(p, t) : xs;
    }
}

lemma void append_take_drop_while(fixpoint(char, bool) p, list<char> xs)
    requires true;
    ensures append(take_while(p, xs), drop_while(p, xs)) == xs;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (p(h)) {
                append_take_drop_while(p, t);
            }
    }
}

lemma void forall_take_while(fixpoint(char, bool) p, list<char> xs)
    requires true;
    ensures forall(take_while(p, xs), p) == true;
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (p(h)) {
                forall_take_while(p, t);
            }
    }
}

lemma void property_drop_while(fixpoint(char, bool) p, list<char> xs)
    requires true;
    ensures drop_while(p, xs) == nil || !p(head(drop_while(p, xs)));
{
    switch (xs) {
        case nil:
        case cons(h, t):
            if (p(h)) {
                property_drop_while(p, t);
            }
    }
}

lemma void forall_append_one(list<char> xs, char c, fixpoint(char, bool) p)
    requires forall(xs, p) == true &*& p(c) == true;
    ensures forall(append(xs, cons(c, nil)), p) == true;
{
    switch(xs) {
        case nil:
        case cons(h, t):
            forall_append_one(t, c, p);
    }
}

predicate charreader_state(list<char> cs);

@*/

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires charreader_state(?cs);
    /*@ ensures
            cs == nil ?
                charreader_state(nil) &*& result == -1
            :
                charreader_state(tail(cs)) &*& result == (int)head(cs) &*& -128 <= result &*& result <= 127;
    @*/

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};

/*@
predicate tokenizer(struct tokenizer* t; list<char> stream, list<char> buffer_content) =
    t->next_char |-> ?reader &*& is_charreader(reader) == true &*&
    t->lastread |-> ?lastread &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?buffer &*& string_buffer(buffer, buffer_content) &*&
    malloc_block_tokenizer(t) &*&
    (
        lastread == -2 ? // buffer empty
            charreader_state(?s) &*& stream == s
        : lastread == -1 ? // EOF
            charreader_state(nil) &*& stream == nil
        : // char in buffer
            -128 <= lastread &*& lastread <= 127 &*&
            charreader_state(?s) &*& stream == cons((char)lastread, s)
    );
@*/


/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(tokenizer, ?s, ?bcs);
//@ ensures tokenizer(tokenizer, s, bcs);
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
{
    //@ open tokenizer(tokenizer, s, bcs);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *reader = tokenizer->next_char;
	        //@ open charreader_state(s);
	        int result = reader();
            //@ switch(s) { case nil: case cons(h, t): }
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
//@ requires tokenizer(tokenizer, ?s, ?bcs);
//@ ensures tokenizer(tokenizer, s, bcs) &*& result == (s == nil ? -1 : (int)head(s));
int tokenizer_peek(struct tokenizer* tokenizer)
{
	tokenizer_fill_buffer(tokenizer);
    //@ open tokenizer(tokenizer, s, bcs);
	int res = tokenizer->lastread;
    //@ if (s == nil) { assert res == -1; } else { assert res == (int)head(s); }
    //@ close tokenizer(tokenizer, s, bcs);
	return res;
}


/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(tokenizer, ?s, ?bcs);
//@ ensures s == nil ? tokenizer(tokenizer, nil, bcs) : tokenizer(tokenizer, tail(s), bcs);
void tokenizer_drop(struct tokenizer* tokenizer)
{
    //@ open tokenizer(tokenizer, s, bcs);
    //@ open charreader_state(?s_underlying);
	tokenizer->lastread = -2;
    //@ if (s == nil) { } else { assert s_underlying == tail(s); }
    //@ close tokenizer(tokenizer, s == nil ? nil : tail(s), bcs);
}


/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(tokenizer, ?s, ?bcs);
/*@ ensures
    s == nil ?
        tokenizer(tokenizer, nil, bcs) &*& result == -1
    :
        tokenizer(tokenizer, tail(s), bcs) &*& result == (int)head(s);
@*/
int tokenizer_next_char(struct tokenizer* tokenizer)
{
	int c;

	tokenizer_fill_buffer(tokenizer);
    //@ open tokenizer(tokenizer, s, bcs);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
    //@ open charreader_state(?s_underlying);
    //@ if (s == nil) { } else { assert s_underlying == tail(s); }
    //@ close tokenizer(tokenizer, s == nil ? nil : tail(s), bcs);
	return c;
}


/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.

This function ensures nothing. 
*/
//@ requires true;
//@ ensures result == is_whitespace(c);
bool is_whitespace(int c)
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


/***
 * Description:
The tokenizer_skip_whitespace function reads and drops all the whitespace characters that are encountered sequentially by the tokenizer.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(t, ?s, ?bcs);
//@ ensures tokenizer(t, drop_while(is_whitespace_char, s), bcs);
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
{
    //@ list<char> s_initial = s;
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
        /*@
        invariant tokenizer(tokenizer, ?s_loop, bcs) &*&
                  s_initial == append(take_while(is_whitespace_char, s_initial), s_loop);
        @*/
	{
        //@ append_take_drop_while(is_whitespace_char, s_loop);
        //@ if (s_loop != nil) { if (is_whitespace_char(head(s_loop))) { take_while_cons(is_whitespace_char, s_loop); } }
		tokenizer_drop(tokenizer);
	}
    //@ property_drop_while(is_whitespace_char, s_loop);
    //@ append_take_drop_while(is_whitespace_char, s_initial);
}


/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.

It ensures nothing.
*/
//@ requires true;
//@ ensures result == is_digit(c);
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


/***
 * Description:
The tokenizer_eat_number function reads all the digit characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and returns the token that represents digit.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(t, ?s, ?bcs_in);
/*@ ensures tokenizer(t, ?s_new, ?bcs_out) &*&
        let num_cs = take_while(is_digit_char, s) in
        s_new == drop_while(is_digit_char, s) &*&
        bcs_out == append(bcs_in, num_cs) &*&
        result == '0';
@*/
int tokenizer_eat_number(struct tokenizer* tokenizer)
{
    //@ list<char> s_initial = s;
	for (;;)
        /*@
        invariant tokenizer(tokenizer, ?s_cur, ?bcs_cur) &*&
                  s_initial == append(drop(length(bcs_in), bcs_cur), s_cur) &*&
                  forall(drop(length(bcs_in), bcs_cur), is_digit_char) == true;
        @*/
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);
		isDigit = is_digit(result);
		if ( !isDigit ) break;
		
	    result = tokenizer_next_char(tokenizer);
        //@ assert s_cur != nil && is_digit_char(head(s_cur));
        //@ forall_append_one(drop(length(bcs_in), bcs_cur), head(s_cur), is_digit_char);
		string_buffer_append_char(tokenizer->buffer, (char)result);
	}
    //@ list<char> num_cs = take_while(is_digit_char, s_initial);
    //@ forall_take_while(is_digit_char, s_initial);
    //@ append_take_drop_while(is_digit_char, s_initial);
    //@ property_drop_while(is_digit_char, s_cur);
	return '0';
}


/***
 * Description:
The is_symbol_char function checks whether a given character in integer means a symbol in ASCII (except parentheses).

It ensures nothing
*/
//@ requires true;
//@ ensures result == is_symbol_char(c);
bool is_symbol_char(int c)
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}


/***
 * Description:
The tokenizer_eat_symbol function reads all the ASCII symbol characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-symbol character, it exits the loop and return the token that represents symbol.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
//@ requires tokenizer(t, ?s, ?bcs_in);
/*@ ensures tokenizer(t, ?s_new, ?bcs_out) &*&
        let sym_cs = take_while(is_symbol_char_char, s) in
        s_new == drop_while(is_symbol_char_char, s) &*&
        bcs_out == append(bcs_in, sym_cs) &*&
        result == 'S';
@*/
int tokenizer_eat_symbol(struct tokenizer* tokenizer)
{
    //@ list<char> s_initial = s;
	for (;;)
        /*@
        invariant tokenizer(tokenizer, ?s_cur, ?bcs_cur) &*&
                  s_initial == append(drop(length(bcs_in), bcs_cur), s_cur) &*&
                  forall(drop(length(bcs_in), bcs_cur), is_symbol_char_char) == true;
        @*/
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) break;
		
		result = tokenizer_next_char(tokenizer);
        //@ assert s_cur != nil && is_symbol_char_char(head(s_cur));
        //@ forall_append_one(drop(length(bcs_in), bcs_cur), head(s_cur), is_symbol_char_char);
		string_buffer_append_char(tokenizer->buffer, (char)result);
	}
    //@ list<char> sym_cs = take_while(is_symbol_char_char, s_initial);
    //@ forall_take_while(is_symbol_char_char, s_initial);
    //@ append_take_drop_while(is_symbol_char_char, s_initial);
    //@ property_drop_while(is_symbol_char_char, s_cur);
	return 'S';
}


/***
 * Description:
The tokenizer_next function gets the next token of the tokenizer by reading the stream sequentially, assigning the token to lasttoken field, and returning it.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
/*@
requires tokenizer(t, ?s, _);
ensures
    let s_after_ws = drop_while(is_whitespace_char, s) in
    s_after_ws == nil ?
        tokenizer(t, nil, nil) &*& result == -1
    :
    let c = head(s_after_ws) in
    (int)c == '(' || (int)c == ')' ?
        tokenizer(t, tail(s_after_ws), nil) &*& result == (int)c
    : is_digit((int)c) ?
        let num_cs = take_while(is_digit_char, s_after_ws) in
        tokenizer(t, drop_while(is_digit_char, s_after_ws), num_cs) &*&
        result == '0'
    : is_symbol_char((int)c) ?
        let sym_cs = take_while(is_symbol_char_char, s_after_ws) in
        tokenizer(t, drop_while(is_symbol_char_char, s_after_ws), sym_cs) &*&
        result == 'S'
    : // bad char
        tokenizer(t, tail(s_after_ws), nil) &*& result == 'B';
@*/
int tokenizer_next(struct tokenizer* tokenizer)
{
	int c;
	int token;

    //@ open tokenizer(tokenizer, s, _);
    //@ struct string_buffer *buffer = tokenizer->buffer;
    //@ open string_buffer(buffer, _);
	string_buffer_clear(tokenizer->buffer);
    //@ close string_buffer(buffer, nil);
    //@ close tokenizer(tokenizer, s, nil);

	tokenizer_skip_whitespace(tokenizer);
    //@ assert tokenizer(tokenizer, ?s_after_ws, nil) &*& s_after_ws == drop_while(is_whitespace_char, s);

	c = tokenizer_peek(tokenizer);
    //@ assert c == (s_after_ws == nil ? -1 : (int)head(s_after_ws));

	if ( c == '(' || c == ')' || c == -1 )
	{
        //@ if (s_after_ws == nil) { assert c == -1; } else { assert c == (int)head(s_after_ws); }
		tokenizer_drop(tokenizer);
        //@ if (s_after_ws == nil) { assert tokenizer(tokenizer, nil, nil); } else { assert tokenizer(tokenizer, tail(s_after_ws), nil); }
		token = c;
	}
	else if ( is_digit(c) )
	{
        //@ assert s_after_ws != nil && is_digit((int)head(s_after_ws));
        //@ assert is_digit_char(head(s_after_ws)) == true;
		token = tokenizer_eat_number(tokenizer);
        //@ let num_cs = take_while(is_digit_char, s_after_ws);
        //@ assert tokenizer(tokenizer, drop_while(is_digit_char, s_after_ws), num_cs);
	}
	else if ( is_symbol_char(c) )
	{
        //@ assert s_after_ws != nil && is_symbol_char((int)head(s_after_ws));
        //@ assert is_symbol_char_char(head(s_after_ws)) == true;
		token = tokenizer_eat_symbol(tokenizer);
        //@ let sym_cs = take_while(is_symbol_char_char, s_after_ws);
        //@ assert tokenizer(tokenizer, drop_while(is_symbol_char_char, s_after_ws), sym_cs);
	}
	else
	{
        //@ assert s_after_ws != nil && !(c == '(' || c == ')' || c == -1 || is_digit(c) || is_symbol_char(c));
		tokenizer_drop(tokenizer);
        //@ assert tokenizer(tokenizer, tail(s_after_ws), nil);
		token = 'B'; // bad character
	}
    //@ open tokenizer(tokenizer, ?s_new, ?bcs);
	tokenizer->lasttoken = token;
    //@ close tokenizer(tokenizer, s_new, bcs);
	return token;
}