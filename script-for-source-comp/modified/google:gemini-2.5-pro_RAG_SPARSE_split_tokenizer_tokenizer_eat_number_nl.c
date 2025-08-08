

struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};


typedef int charreader();


void tokenizer_fill_buffer(struct tokenizer* tokenizer)
{
	if ( tokenizer->lastread == -2 )
	{
	        charreader *rd = tokenizer->next_char;
	        int result = rd();
		if (result < -128 || result > 127)
			abort();
		tokenizer->lastread = result;
	}
}


int tokenizer_peek(struct tokenizer* tokenizer)
{
	tokenizer_fill_buffer(tokenizer);
	int res = tokenizer->lastread;
	return res;
}


int tokenizer_next_char(struct tokenizer* tokenizer)
{
	int c;

	tokenizer_fill_buffer(tokenizer);
	c = tokenizer->lastread;
	tokenizer->lastread = -2;
	return c;
}


bool is_digit(int c)
{
	return c >= '0' && c <= '9';
}


void string_buffer_append_char(struct string_buffer *buffer, char c)
{
	char cc = c;
	string_buffer_append_chars(buffer, &cc, 1);
}


int tokenizer_eat_number(struct tokenizer* tokenizer)
{

	for (;;)
	{
		int result;
		bool isDigit;
		
		result = tokenizer_peek(tokenizer);

		isDigit = is_digit(result);
		
		if ( !isDigit ) {
            break;
        }
		

	    result = tokenizer_next_char(tokenizer);

		string_buffer_append_char(tokenizer->buffer, (char)result);
	}

	return '0';
}
