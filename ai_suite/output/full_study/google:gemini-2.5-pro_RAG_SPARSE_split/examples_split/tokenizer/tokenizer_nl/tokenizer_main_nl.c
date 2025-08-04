#include "stdio.h"
#include "stdlib.hh"
#include "stringBuffers.h"

/*@
// VeriFast-specific includes for ghost code
#include <list.gh>

// --- Predicates and Function Types for Verification ---

// A charreader is a function that reads a character from an abstract stream.
// It returns -1 on EOF. The characters are in the range [-128, 127].
typedef int charreader();
    requires charreader(this, ?s);
    ensures
        s == nil ?
            charreader(this, nil) &*& result == -1
        :
            charreader(this, tail(s)) &*& result == head(s) &*& -128 <= result &*& result <= 127;

// Predicate to link a concrete function (my_getchar) to the abstract charreader interface.
predicate_family charreader_data(void* f)(list<char> s);
predicate charreader(charreader* f, list<char> s) = charreader_data(f)(s);

// Abstract model for stdin.
predicate input_stream(list<char> cs);

// Predicate for the state of the tokenizer's internal reader.
predicate tokenizer_state(charreader *reader, int lastread, list<char> stream) =
    is_charreader(reader) == true &*&
    (
        lastread == -2 ?
            charreader(reader, stream)
        : lastread == -1 ?
            stream == nil &*& charreader(reader, nil)
        :
            stream != nil &*& head(stream) == lastread &*& charreader(reader, tail(stream))
    );

// Predicate representing a valid tokenizer object, split for easier manipulation.
predicate tokenizer_no_buffer(struct tokenizer *t; list<char> stream) =
    t->next_char |-> ?reader &*&
    t->lastread |-> ?lastread &*&
    t->lasttoken |-> ?lasttoken &*&
    t->buffer |-> ?buffer &*&
    malloc_block_tokenizer(t) &*&
    tokenizer_state(reader, lastread, stream);

predicate tokenizer(struct tokenizer *t; list<char> stream, list<char> buffer_content) =
    tokenizer_no_buffer(t, stream) &*&
    string_buffer(t->buffer, buffer_content);

// --- Helper Fixpoint Functions for Specifications ---

fixpoint bool is_whitespace_int(int c) { return c == ' ' || c == '\n' || c == '\r' || c == '\t'; }
fixpoint bool is_digit_int(int c) { return c >= '0' && c <= '9'; }
fixpoint bool is_symbol_char_int(int c) { return c > 32 && c <= 127 && c != '(' && c != ')'; }

fixpoint bool is_whitespace_char(char c) { return is_whitespace_int(c); }
fixpoint bool is_digit_char(char c) { return is_digit_int(c); }
fixpoint bool is_symbol_char_char(char c) { return is_symbol_char_int(c); }

fixpoint list<t> take_while<t>(fixpoint(t, bool) p, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return p(h) ? cons(h, take_while(p, t)) : nil;
    }
}

lemma void take_while_cons<t>(fixpoint(t, bool) p, list<t> xs);
    requires xs == cons(?h, ?t);
    ensures take_while(p, xs) == (p(h) ? cons(h, take_while(p, t)) : nil);

fixpoint list<t> drop_while<t>(fixpoint(t, bool) p, list<t> xs) {
    switch (xs) {
        case nil: return nil;
        case cons(h, t): return p(h) ? drop_while(p, t) : xs;
    }
}

lemma void drop_while_cons<t>(fixpoint(t, bool) p, list<t> xs);
    requires xs == cons(?h, ?t);
    ensures drop_while(p, xs) == (p(h) ? drop_while(p, t) : xs);

lemma void take_append_drop_while<t>(fixpoint(t, bool) p, list<t> xs);
    requires true;
    ensures append(take_while(p, xs), drop_while(p, xs)) == xs;

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
    //@ open tokenizer_no_buffer(tokenizer, s);
	if ( tokenizer->lastread == -2 )
	{
	    charreader *reader = tokenizer->next_char;
        //@ open tokenizer_state(reader, -2, s);
	    int result = reader();
		if (result < -128 || result > 127)
			abort();
		tokenizer->lastread = result;
        //@ if (s == nil) { } else { }
        //@ close tokenizer_state(reader, result, s);
	}
    //@ close tokenizer_no_buffer(tokenizer, s);
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
    //@ open tokenizer_no_buffer(tokenizer, s);
	int result = tokenizer->lastread;
    //@ close tokenizer_no_buffer(tokenizer, s);
    //@ close tokenizer(tokenizer, s, bcs);
	return result;
}


/***
 * Description:
The tokenizer_drop function drops the last character of a tokenizer by assigning its lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_drop(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, s == nil ? nil : tail(s), bcs);
{
    //@ open tokenizer(tokenizer, s, bcs);
    //@ open tokenizer_no_buffer(tokenizer, s);
    charreader *reader = tokenizer->next_char;
    int lastread = tokenizer->lastread;
    //@ open tokenizer_state(reader, lastread, s);
	tokenizer->lastread = -2;
    //@ if (s == nil) { } else { }
    //@ close tokenizer_state(reader, -2, s == nil ? nil : tail(s));
    //@ close tokenizer_no_buffer(tokenizer, s == nil ? nil : tail(s));
    //@ close tokenizer(tokenizer, s == nil ? nil : tail(s), bcs);
}


/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures s == nil ? tokenizer(tokenizer, nil, bcs) &*& result == -1 : tokenizer(tokenizer, tail(s), bcs) &*& result == head(s);
{
	int c;

	tokenizer_fill_buffer(tokenizer);
    //@ open tokenizer(tokenizer, s, bcs);
    //@ open tokenizer_no_buffer(tokenizer, s);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
    charreader *reader = tokenizer->next_char;
    //@ open tokenizer_state(reader, c, s);
    //@ if (s == nil) { } else { }
    //@ close tokenizer_state(reader, -2, s == nil ? nil : tail(s));
    //@ close tokenizer_no_buffer(tokenizer, s == nil ? nil : tail(s));
    //@ close tokenizer(tokenizer, s == nil ? nil : tail(s), bcs);
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
    //@ ensures tokenizer(tokenizer, drop_while(is_whitespace_int, s), bcs);
{
    //@ list<char> s_loop = s;
	while ( is_whitespace( tokenizer_peek(tokenizer) ) )
        /*@
        invariant tokenizer(tokenizer, s_loop, bcs) &*&
                  append(take_while(is_whitespace_int, s), s_loop) == s;
        decreases length(s_loop);
        @*/
	{
        //@ assert s_loop != nil && is_whitespace_int(head(s_loop)) == true;
		tokenizer_drop(tokenizer);
        //@ take_while_cons(is_whitespace_int, s_loop);
        //@ s_loop = tail(s_loop);
	}
    //@ assert s_loop == drop_while(is_whitespace_int, s_loop);
    //@ take_append_drop_while(is_whitespace_int, s);
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
	string_buffer_append_chars(buffer, &cc, 1);
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
    //@ ensures tokenizer(tokenizer, drop_while(is_digit_int, s), append(bcs, take_while(is_digit_int, s))) &*& result == '0';
{
    //@ list<char> s_initial = s;
    //@ list<char> bcs_initial = bcs;
	for (;;)
        /*@
        invariant tokenizer(tokenizer, ?s_loop, ?bcs_loop) &*&
                  drop_while(is_digit_int, s_initial) == s_loop &*&
                  append(bcs_initial, take_while(is_digit_int, s_initial)) == bcs_loop;
        decreases length(s_loop);
        @*/
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);
		isDigit = is_digit(result);
		if ( !isDigit ) break;
		
	    result = tokenizer_next_char(tokenizer);
        //@ open tokenizer(tokenizer, s_loop, bcs_loop);
        //@ open tokenizer_no_buffer(tokenizer, s_loop);
        //@ struct string_buffer *b = tokenizer->buffer;
		string_buffer_append_char(b, (char)result);
        //@ close tokenizer_no_buffer(tokenizer, tail(s_loop));
        //@ close tokenizer(tokenizer, tail(s_loop), append(bcs_loop, cons((char)result, nil)));
        
        //@ assert s_loop != nil && is_digit_int(head(s_loop));
        //@ take_while_cons(is_digit_int, s_loop);
        //@ drop_while_cons(is_digit_int, s_loop);
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
    //@ ensures tokenizer(tokenizer, drop_while(is_symbol_char_int, s), append(bcs, take_while(is_symbol_char_int, s))) &*& result == 'S';
{
    //@ list<char> s_initial = s;
    //@ list<char> bcs_initial = bcs;
	for (;;)
        /*@
        invariant tokenizer(tokenizer, ?s_loop, ?bcs_loop) &*&
                  drop_while(is_symbol_char_int, s_initial) == s_loop &*&
                  append(bcs_initial, take_while(is_symbol_char_int, s_initial)) == bcs_loop;
        decreases length(s_loop);
        @*/
	{
		int result;
		bool isSymbolChar;
		
		result = tokenizer_peek(tokenizer);
		isSymbolChar = is_symbol_char(result);
		
		if (!isSymbolChar) break;
		
		result = tokenizer_next_char(tokenizer);
        //@ open tokenizer(tokenizer, s_loop, bcs_loop);
        //@ open tokenizer_no_buffer(tokenizer, s_loop);
        //@ struct string_buffer *b = tokenizer->buffer;
		string_buffer_append_char(tokenizer->buffer, (char)result);
        //@ close tokenizer_no_buffer(tokenizer, tail(s_loop));
        //@ close tokenizer(tokenizer, tail(s_loop), append(bcs_loop, cons((char)result, nil)));

        //@ assert s_loop != nil && is_symbol_char_int(head(s_loop));
        //@ take_while_cons(is_symbol_char_int, s_loop);
        //@ drop_while_cons(is_symbol_char_int, s_loop);
	}

	return 'S';
}


/***
 * Description:
The tokenizer_next function gets the next token of the tokenizer by reading the stream sequentially, assigning the token to lasttoken field, and returning it.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, _, _);
{
	int c;
	int token;

    //@ open tokenizer(tokenizer, s, bcs);
    //@ struct string_buffer *b = tokenizer->buffer;
	string_buffer_clear(b);
    //@ close tokenizer(tokenizer, s, nil);

	tokenizer_skip_whitespace(tokenizer);
    //@ take_append_drop_while(is_whitespace_int, s);

	c = tokenizer_peek(tokenizer);

	if ( c == '(' || c == ')' || c == -1 )
	{
		tokenizer_drop(tokenizer);
		token = c;
	}
	else if ( is_digit(c) )
	{
		token = tokenizer_eat_number(tokenizer);
        //@ take_append_drop_while(is_digit_int, drop_while(is_whitespace_int, s));
	}
	else if ( is_symbol_char(c) )
	{
		token = tokenizer_eat_symbol(tokenizer);
        //@ take_append_drop_while(is_symbol_char_int, drop_while(is_whitespace_int, s));
	}
	else
	{
		tokenizer_drop(tokenizer);
		token = 'B'; // bad character
	}
    //@ open tokenizer(tokenizer, _, _);
    //@ open tokenizer_no_buffer(tokenizer, _);
	tokenizer->lasttoken = token;
    //@ close tokenizer_no_buffer(tokenizer, _);
    //@ close tokenizer(tokenizer, _, _);
	return token;
}


/***
 * Description:
The tokenizer_create function creates a tokenizer given a charreader.

It needs to make sure that the returned tokenizer preserves its property of tokenizer. 
*/
struct tokenizer* tokenizer_create(charreader* reader)
    //@ requires is_charreader(reader) == true &*& charreader(reader, ?s);
    //@ ensures tokenizer(result, s, nil);
{
	struct tokenizer* tokenizer;
	struct string_buffer *buffer;
	
	tokenizer = (struct tokenizer*) malloc( sizeof( struct tokenizer ) );
	if ( tokenizer == 0 ) abort();
	tokenizer->lastread = -2;
	tokenizer->lasttoken = 0;
	tokenizer->next_char = reader;
	buffer = create_string_buffer();
	tokenizer->buffer = buffer;
    //@ close tokenizer_state(reader, -2, s);
    //@ close tokenizer_no_buffer(tokenizer, s);
    //@ close tokenizer(tokenizer, s, nil);
	return tokenizer;
}


/***
 * Description:
The tokenizer_dispose function frees the tokenizer.

It needs to make sure that the given tokenizer is freed.
*/
void tokenizer_dispose(struct tokenizer *tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures charreader(tokenizer->next_char, _);
{
    //@ open tokenizer(tokenizer, s, bcs);
    //@ open tokenizer_no_buffer(tokenizer, s);
	string_buffer_dispose(tokenizer->buffer);
    //@ open tokenizer_state(tokenizer->next_char, _, s);
	free(tokenizer);
}


/***
 * Description:
The print_string_buffer function prints the content in a string buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void print_string_buffer(struct string_buffer *buffer)
    //@ requires string_buffer(buffer, ?cs);
    //@ ensures string_buffer(buffer, cs);
{
	int n = string_buffer_get_length(buffer);
	char *pcs = string_buffer_get_chars(buffer);
	int i;
	for (i = 0; i < n; i++)
        //@ invariant string_buffer_minus_chars(buffer, pcs, n) &*& chars(pcs, n, cs) &*& 0 <= i &*& i <= n;
	{
        //@ chars_split(pcs, i);
        //@ open chars(pcs + i, n - i, _);
		putchar(pcs[i]);
        //@ close chars(pcs + i, n - i, _);
        //@ chars_join(pcs);
	}
    //@ string_buffer_merge_chars(buffer);
}


/***
 * Description:
The print_token function prints the last token of of a tokenizer by reading its lasttoken field and prints a readable content of the token.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void print_token(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?s, ?bcs);
    //@ ensures tokenizer(tokenizer, s, bcs);
{
    //@ open tokenizer(tokenizer, s, bcs);
    //@ open tokenizer_no_buffer(tokenizer, s);
	switch ( tokenizer->lasttoken )
	{
	case '(':
		puts("LPAREN");
		break;

	case ')':
		puts("RPAREN");
		break;

	case '0':
		putchar('N');
		print_string_buffer(tokenizer->buffer);
		puts("");
		break;

	case 'S':
		putchar('S');
		print_string_buffer(tokenizer->buffer);
		puts("");
		break;
	
	case 'B':
		puts("BADCHAR");
		break;
	}
    //@ close tokenizer_no_buffer(tokenizer, s);
    //@ close tokenizer(tokenizer, s, bcs);
}


/***
 * Description:
The my_getchar function acts as a char reader and returns an integer read.

It ensures nothing.
*/
//@ predicate_family_instance charreader_data(my_getchar)(list<char> s) = input_stream(s);
int my_getchar() //@ : charreader
{
	return getchar();
}


// TODO: make this function pass the verification
/***
 * Description:
The main function tests the functionality of tokenizer operations.
It first creates a tokenizer, then continues reading and printing the tokens,
and finally free the tokenizer.
*/
int main()
    //@ requires true;
    //@ ensures true;
{
    //@ close input_stream(cons('(', cons('1', cons('2', cons(')', nil)))));
	struct tokenizer* tokenizer = tokenizer_create(my_getchar);

	for (;;)
        //@ invariant tokenizer(tokenizer, ?s, _);
        //@ decreases length(s);
	{
		int result = tokenizer_next(tokenizer);
		if (result == -1) break;
		print_token(tokenizer);
	}
	
	tokenizer_dispose(tokenizer);
    //@ leak input_stream(_);

	puts("The end");
	return 0;
}