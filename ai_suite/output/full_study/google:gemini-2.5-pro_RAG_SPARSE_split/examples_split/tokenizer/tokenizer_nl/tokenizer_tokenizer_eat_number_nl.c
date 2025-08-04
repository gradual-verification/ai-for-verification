#include "stdio.h"
#include "stdlib.hh"
#include "stringBuffers.h"

/*@
// Predicates and fixpoints for verification

fixpoint bool is_digit_spec(int c) { return c >= '0' && c <= '9'; }

// Model for the abstract character reader
predicate charreader(charreader* f; list<int> stream);

typedef int charreader_code();
    requires charreader(this, ?s);
    ensures
        charreader(this, s == nil ? nil : tail(s)) &*&
        result == (s == nil ? -1 : head(s)) &*&
        // The implementation checks this range.
        result >= -128 &*& result <= 127;

// Predicate for the tokenizer struct
predicate tokenizer(struct tokenizer *t; charreader* reader, list<int> stream, int lastread, list<char> buffer_content) =
    t->next_char |-> reader &*&
    is_charreader_code(reader) == true &*& charreader(reader, stream) &*&
    t->lastread |-> lastread &*&
    t->lasttoken |-> _ &*&
    t->buffer |-> ?buffer &*&
    string_buffer(buffer, buffer_content) &*&
    lastread >= -2 &*& lastread <= 127 &*&
    (lastread == -1 ? stream == nil : true);

// The logical stream of characters available from the tokenizer
fixpoint list<int> available_stream(int lastread, list<int> stream) {
    if (lastread >= 0)
        return cons(lastread, stream);
    else if (lastread == -1)
        return nil;
    else // lastread == -2
        return stream;
}

// Splits a stream into a prefix of digits and the remainder
fixpoint pair<list<int>, list<int> > split_digits(list<int> stream) {
    if (stream == nil) {
        return pair(nil, nil);
    } else {
        int h = head(stream);
        if (is_digit_spec(h)) {
            pair<list<int>, list<int> > p = split_digits(tail(stream));
            return pair(cons(h, fst(p)), snd(p));
        } else {
            return pair(nil, stream);
        }
    }
}

// Converts a list of ints to a list of chars
fixpoint list<char> int_list_to_char_list(list<int> is) {
    switch (is) {
        case nil: return nil;
        case cons(h, t): return cons((char)h, int_list_to_char_list(t));
    }
}

// Lemma: forall(map(f, xs), p) == forall(xs, (compose)(p, f))
lemma_auto void forall_map<a,b>(list<a> xs, fixpoint(a,b) f, fixpoint(b,bool) p)
    requires true;
    ensures forall(map(f, xs), p) == forall(xs, (compose)(p, f));
{
    switch(xs) {
        case nil:
        case cons(h,t):
            forall_map(t, f, p);
    }
}

// Lemma for reasoning about split_digits on a prefixed stream
lemma void split_digits_prefix(list<int> prefix, list<int> rest)
    requires forall(prefix, (is_digit_spec)) == true;
    ensures split_digits(append(prefix, rest)) == pair(append(prefix, fst(split_digits(rest))), snd(split_digits(rest)));
{
    switch (prefix) {
        case nil:
        case cons(h, t):
            open forall(prefix, (is_digit_spec));
            split_digits_prefix(t, rest);
    }
}

// Lemma showing that available_stream is invariant under tokenizer_fill_buffer
lemma void available_stream_fill_buffer_commutes(int lr, list<int> s)
    requires true;
    ensures available_stream(
        lr == -2 ? (s == nil ? -1 : head(s)) : lr,
        lr == -2 ? (s == nil ? nil : tail(s)) : s
    ) == available_stream(lr, s);
{
    if (lr == -2) {
        if (s == nil) {
        } else {
        }
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


/***
 * Description:
The tokenizer_fill_buffer function reads a character from the next_char reader of the tokenizer and updates the lastread char,
if the original lastread char is -2 (which means empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
void tokenizer_fill_buffer(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?s, ?lr, ?bcs);
    /*@ ensures tokenizer(tokenizer, reader, ?s_new, ?lr_new, bcs) &*&
                (lr == -2 ?
                    (s_new == (s == nil ? nil : tail(s)) &*& lr_new == (s == nil ? -1 : head(s)))
                :
                    (s_new == s &*& lr_new == lr));
    @*/
{
	//@ open tokenizer(tokenizer, reader, s, lr, bcs);
	if ( tokenizer->lastread == -2 )
	{
	        charreader *rd = tokenizer->next_char;
	        //@ open charreader(rd, s);
	        int result = rd();
	        //@ close charreader(rd, s == nil ? nil : tail(s));
		if (result < -128 || result > 127)
			abort();
		tokenizer->lastread = result;
	}
	//@ close tokenizer(tokenizer, reader, _, _, bcs);
}


/***
 * Description:
The tokenizer_peek function reads the next value character of a tokenizer and returns the updated lastread character.

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_peek(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?s, ?lr, ?bcs);
    /*@ ensures tokenizer(tokenizer, reader, ?s_new, ?lr_new, bcs) &*&
                (lr == -2 ?
                    (s_new == (s == nil ? nil : tail(s)) &*& lr_new == (s == nil ? -1 : head(s)) &*& result == lr_new)
                :
                    (s_new == s &*& lr_new == lr &*& result == lr));
    @*/
{
	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, reader, _, _, bcs);
	int res = tokenizer->lastread;
	//@ close tokenizer(tokenizer, reader, _, _, bcs);
	return res;
}


/***
 * Description:
The tokenizer_next_char function reads the next character of a tokenizer, returns that character 
and drops that character by assigning the lastread field to -2 (meaning empty).

It needs to make sure that the given tokenizer preserves its property of tokenizer. 
*/
int tokenizer_next_char(struct tokenizer* tokenizer)
    //@ requires tokenizer(tokenizer, ?reader, ?s, ?lr, ?bcs);
    /*@ ensures tokenizer(tokenizer, reader, ?s_new, -2, bcs) &*&
                (lr == -2 ?
                    (s_new == (s == nil ? nil : tail(s)) &*& result == (s == nil ? -1 : head(s)))
                :
                    (s_new == s &*& result == lr));
    @*/
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	//@ open tokenizer(tokenizer, ?reader_, ?s_filled, ?lr_filled, ?bcs_filled);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	//@ close tokenizer(tokenizer, reader_, s_filled, -2, bcs_filled);
	return c;
}


/***
 * Description:
The is_digit function checks whether a given character in integer means a digit number.

It ensures nothing.
*/
bool is_digit(int c)
    //@ requires true;
    //@ ensures result == is_digit_spec(c);
{
	return c >= '0' && c <= '9';
}


/***
 * Description:
The string_buffer_append_char function appends a char to a buffer.

It needs to make sure that the property of the buffer holds (i.e., the buffer points to a list of characters) before and after the function.
*/
void string_buffer_append_char(struct string_buffer *buffer, char c)
    //@ requires string_buffer(buffer, ?bcs);
    //@ ensures string_buffer(buffer, append(bcs, cons(c, nil)));
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
int tokenizer_eat_number(struct tokenizer* tokenizer)
    /*@
    requires tokenizer(tokenizer, ?reader, ?s, ?lr, ?bcs);
    ensures
        let initial_stream = available_stream(lr, s) in
        let p = split_digits(initial_stream) in
        let ds = fst(p) in
        let rem = snd(p) in
        tokenizer(tokenizer, reader, ?s_final, ?lr_final, append(bcs, int_list_to_char_list(ds))) &*&
        available_stream(lr_final, s_final) == rem &*&
        result == '0';
    @*/
{
    //@ open tokenizer(tokenizer, reader, s, lr, bcs);
    //@ let initial_stream = available_stream(lr, s);
    //@ let p = split_digits(initial_stream);
    //@ let ds = fst(p);
    //@ let rem = snd(p);
    //@ close tokenizer(tokenizer, reader, s, lr, bcs);
    //@ list<int> ds_read = nil;
    //@ forall_nil((is_digit_spec));
    //@ split_digits_prefix(ds_read, initial_stream);

	for (;;)
        /*@
        invariant
            tokenizer(tokenizer, ?reader_curr, ?s_curr, ?lr_curr, ?bcs_curr) &*&
            reader == reader_curr &*&
            bcs_curr == append(bcs, int_list_to_char_list(ds_read)) &*&
            initial_stream == append(ds_read, available_stream(lr_curr, s_curr)) &*&
            ds == append(ds_read, fst(split_digits(available_stream(lr_curr, s_curr)))) &*&
            rem == snd(split_digits(available_stream(lr_curr, s_curr))) &*&
            forall(ds_read, (is_digit_spec)) == true;
        @*/
	{
		int result;
		bool isDigit;
		
        //@ let current_available = available_stream(lr_curr, s_curr);
        //@ available_stream_fill_buffer_commutes(lr_curr, s_curr);
		result = tokenizer_peek(tokenizer);
        //@ open tokenizer(tokenizer, reader_curr, ?s_peek, ?lr_peek, bcs_curr);
        //@ close tokenizer(tokenizer, reader_curr, s_peek, lr_peek, bcs_curr);
        //@ assert available_stream(lr_peek, s_peek) == current_available;

		isDigit = is_digit(result);
        //@ assert isDigit == is_digit_spec(result);
        //@ assert result == lr_peek;
		
		if ( !isDigit ) {
            //@ assert is_digit_spec(lr_peek) == false;
            /*@
            if (current_available == nil) {
                assert lr_peek == -1;
            } else {
                assert head(current_available) == lr_peek;
            }
            @*/
            //@ assert fst(split_digits(current_available)) == nil;
            //@ assert snd(split_digits(current_available)) == current_available;
            break;
        }
		
        //@ assert is_digit_spec(lr_peek) == true;
        /*@
        if (current_available == nil) {
            // This case is impossible, because lr_peek would be -1, which is not a digit.
            assert false;
        } else {
            assert head(current_available) == lr_peek;
        }
        @*/
        //@ assert fst(split_digits(current_available)) == cons(lr_peek, fst(split_digits(tail(current_available))));
        //@ assert snd(split_digits(current_available)) == snd(split_digits(tail(current_available)));

	    result = tokenizer_next_char(tokenizer);
        //@ open tokenizer(tokenizer, reader_curr, ?s_next, ?lr_next, bcs_curr);
        //@ assert lr_next == -2;
        //@ assert result == lr_peek;
        //@ assert available_stream(lr_next, s_next) == tail(current_available);
        //@ close tokenizer(tokenizer, reader_curr, s_next, lr_next, bcs_curr);

		string_buffer_append_char(tokenizer->buffer, (char)result);
        //@ ds_read = append(ds_read, cons(result, nil));
        //@ forall_append(ds_read, cons(result, nil), (is_digit_spec));
	}

	return '0';
}