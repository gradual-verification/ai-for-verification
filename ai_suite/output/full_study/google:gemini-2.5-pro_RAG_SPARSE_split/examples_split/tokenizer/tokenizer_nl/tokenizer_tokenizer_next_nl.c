#include "stdio.h"
#include "stdlib.h"
#include "stringBuffers.h"

/*@
// VeriFast specification starts here

// --- Fixpoint helper functions for classifying characters ---

fixpoint bool is_whitespace_int(int c) { return c == ' ' || c == '\n' || c == '\r' || c == '\t'; }
fixpoint bool is_digit_int(int c) { return c >= '0' && c <= '9'; }
fixpoint bool is_symbol_char_int(int c) { return c > 32 && c <= 127 && c != '(' && c != ')'; }

// --- Fixpoint helper functions for list manipulation ---

fixpoint list<t> drop_while<t>(list<t> s, fixpoint(t, bool) p) {
    switch(s) {
        case nil: return nil;
        case cons(h, t): return p(h) ? drop_while(t, p) : s;
    }
}

fixpoint list<t> take_while<t>(list<t> s, fixpoint(t, bool) p) {
    switch(s) {
        case nil: return nil;
        case cons(h, t): return p(h) ? cons(h, take_while(t, p)) : nil;
    }
}

lemma void take_while_append_drop_while<t>(list<t> s, fixpoint(t, bool) p)
    requires true;
    ensures append(take_while(s, p), drop_while(s, p)) == s;
{
    switch(s) {
        case nil:
        case cons(h, t):
            if (!p(h)) {
            } else {
                take_while_append_drop_while(t, p);
            }
    }
}

fixpoint char char_of_int(int c) { return (char)c; }

// --- Predicates and typedefs for the tokenizer ---

predicate charreader_pred(charreader* f; list<int> stream);

@*/

/***
 * Description:
The charreader is a function that reads a character and returns it in an integer.
*/
typedef int charreader();
    //@ requires charreader_pred(this, ?s);
    //@ ensures s == nil ? charreader_pred(this, nil) &*& result == -1 : charreader_pred(this, tail(s)) &*& result == head(s) &*& -128 <= result &*& result <= 127;

/*@
predicate is_charreader(charreader* f) = true;

predicate tokenizer(struct tokenizer *t; list<int> stream, list<char> buffer_cs) =
    t->next_char |-> ?reader &*& is_charreader(reader) == true &*&
    t->lastread |-> ?lastread &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?buffer &*&
    string_buffer(buffer, buffer_cs) &*&
    malloc_block_tokenizer(t) &*&
    (lastread == -2 ?
        // Buffer is empty, the full stream is in the reader
        charreader_pred(reader, stream)
    : lastread == -1 ?
        // EOF has been read
        stream == nil &*& charreader_pred(reader, nil)
    :
        // A character is buffered in lastread
        stream == cons(lastread, ?rest) &*& charreader_pred(reader, rest)
    );

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
	        //@ open charreader_pred(reader, s);
	        int result = reader();
	        //@ if (s == nil) { close charreader_pred(reader, nil); } else { close charreader_pred(reader, tail(s)); }
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
	//@ if (s == nil) { assert tokenizer->lastread |-> -1; } else { assert tokenizer->lastread |-> head(s); }
	int c = tokenizer->lastread;
	//@ close tokenizer(tokenizer, s, bcs);
	return c;
}


/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, s == nil ? s : tail(s), bcs);
{
    tokenizer_fill_buffer(tokenizer);
    //@ open tokenizer(tokenizer, s, bcs);
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, tail(s), bcs);
}


/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, tail(s), bcs) &*& result == (s == nil ? -1 : head(s));
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, s, bcs);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, tail(s), bcs);
	return c;
}


/***
 * Description:
The is_whitespace function checks whether a given character in integer means a whitespace.

This function ensures nothing. 
*/
bool is_whitespace(int c)
    //@ requires true;
    //@ ensures result == is_whitespace_int(c);
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


/***
 * Description:
The tokenizer_skip_whitespace function reads and drops all the whitespace characters that are encountered sequentially by the tokenizer.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, drop_while(s, is_whitespace_int), bcs);
{
    //@ take_while_append_drop_while(s, is_whitespace_int);
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
	    /*@
	    invariant
	        tokenizer(tokenizer, ?current_s, bcs) &*&
	        drop_while(s, is_whitespace_int) == drop_while(current_s, is_whitespace_int) &*&
	        is_whitespace_int(head(current_s)) ? true : drop_while(current_s, is_whitespace_int) == current_s;
	    @*/
	{
		tokenizer_drop(tokenizer);
	}
}


/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.

It ensures nothing.
*/
bool is_digit(int c)
    //@ requires true;
    //@ ensures result == is_digit_int(c);
{
	return c >= '0' && c <= '9';
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
	//@ character_limits(&cc);
	//@ open character(&cc, c);
	//@ close chars(&cc + 1, 0, nil);
	string_buffer_append_chars(buffer, &cc, 1);
	//@ open chars(&cc, 1, _);
	//@ leak character(&cc, c) &*& chars(&cc + 1, 0, _);
}


/***
 * Description:
The tokenizer_eat_number function reads all the digit characters that are encountered sequentially by the tokenizer, 
and adds them into the buffer at the same time.
If it peeks a non-digit character, it exits the loop and returns the token that represents digit.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_eat_number(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, drop_while(s, is_digit_int), append(bcs, map(char_of_int, take_while(s, is_digit_int)))) &*& result == '0';
{
    //@ take_while_append_drop_while(s, is_digit_int);
	for (;;)
	    /*@
	    invariant
	        tokenizer(tokenizer, ?current_s, ?current_bcs) &*&
	        s == append(eaten, current_s) &*&
	        current_bcs == append(bcs, map(char_of_int, eaten)) &*&
	        forall(eaten, is_digit_int) == true &*&
	        take_while(s, is_digit_int) == eaten &*&
	        drop_while(s, is_digit_int) == current_s;
	    @*/
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);
		isDigit = is_digit(result);
		if ( !isDigit ) break;
		
	    result = tokenizer_next_char(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
		//@ take_while_append_drop_while(tail(current_s), is_digit_int);
	}

	return '0';
}


/***
 * Description:
The is_symbol_char function checks whether a given character in integer means a symbol in ASCII (except parentheses).

It ensures nothing
*/
bool is_symbol_char(int c)
    //@ requires true;
    //@ ensures result == is_symbol_char_int(c);
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
int tokenizer_eat_symbol(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, drop_while(s, is_symbol_char_int), append(bcs, map(char_of_int, take_while(s, is_symbol_char_int)))) &*& result == 'S';
{
    //@ take_while_append_drop_while(s, is_symbol_char_int);
	for (;;)
	    /*@
	    invariant
	        tokenizer(tokenizer, ?current_s, ?current_bcs) &*&
	        s == append(eaten, current_s) &*&
	        current_bcs == append(bcs, map(char_of_int, eaten)) &*&
	        forall(eaten, is_symbol_char_int) == true &*&
	        take_while(s, is_symbol_char_int) == eaten &*&
	        drop_while(s, is_symbol_char_int) == current_s;
	    @*/
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) break;
		
		result = tokenizer_next_char(tokenizer);
		string_buffer_append_char(tokenizer->buffer, (char)result);
		//@ take_while_append_drop_while(tail(current_s), is_symbol_char_int);
	}

	return 'S';
}

/*@
fixpoint pair<int, pair<list<int>, list<char>>> parse_next_token(list<int> s) {
    let s_ws = drop_while(s, is_whitespace_int);
    if (s_ws == nil) return pair(-1, pair(nil, nil));
    let c = head(s_ws);
    let s_tail = tail(s_ws);
    if (c == '(' || c == ')') return pair(c, pair(s_tail, nil));
    if (is_digit_int(c)) {
        let num_is = take_while(s_ws, is_digit_int);
        return pair('0', pair(drop(length(num_is), s_ws), map(char_of_int, num_is)));
    }
    if (is_symbol_char_int(c)) {
        let sym_is = take_while(s_ws, is_symbol_char_int);
        return pair('S', pair(drop(length(sym_is), s_ws), map(char_of_int, sym_is)));
    }
    return pair('B', pair(s_tail, nil));
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The tokenizer_next function gets the next token of the tokenizer by reading the stream sequentially, assigning the token to lasttoken field, and returning it.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, _);
    /*@ ensures
            let p = parse_next_token(s);
            let token_val = fst(p);
            let s_new = fst(snd(p));
            let bcs_new = snd(snd(p));
            tokenizer(tokenizer, s_new, bcs_new) &*&
            result == token_val &*&
            tokenizer->lasttoken |-> token_val;
    @*/
{
	int c;
	int token;

    //@ open tokenizer(tokenizer, s, _);
	string_buffer_clear(tokenizer->buffer);
	//@ close tokenizer(tokenizer, s, nil);

	tokenizer_skip_whitespace(tokenizer);
    //@ let s_ws = drop_while(s, is_whitespace_int);
    //@ assert tokenizer(tokenizer, s_ws, nil);

	c = tokenizer_peek(tokenizer);
    //@ assert c == (s_ws == nil ? -1 : head(s_ws));

	if ( c == '(' || c == ')' || c == -1 )
	{
		tokenizer_drop(tokenizer);
        //@ assert tokenizer(tokenizer, tail(s_ws), nil);
		token = c;
	}
	else if ( is_digit(c) )
	{
		token = tokenizer_eat_number(tokenizer);
        //@ let num_is = take_while(s_ws, is_digit_int);
        //@ let s_new = drop_while(s_ws, is_digit_int);
        //@ assert tokenizer(tokenizer, s_new, map(char_of_int, num_is));
	}
	else if ( is_symbol_char(c) )
	{
		token = tokenizer_eat_symbol(tokenizer);
        //@ let sym_is = take_while(s_ws, is_symbol_char_int);
        //@ let s_new = drop_while(s_ws, is_symbol_char_int);
        //@ assert tokenizer(tokenizer, s_new, map(char_of_int, sym_is));
	}
	else
	{
		tokenizer_drop(tokenizer);
        //@ assert tokenizer(tokenizer, tail(s_ws), nil);
		token = 'B'; // bad character
	}
    //@ open tokenizer(tokenizer, ?s_final, ?bcs_final);
	tokenizer->lasttoken = token;
    //@ close tokenizer(tokenizer, s_final, bcs_final);
	return token;
}