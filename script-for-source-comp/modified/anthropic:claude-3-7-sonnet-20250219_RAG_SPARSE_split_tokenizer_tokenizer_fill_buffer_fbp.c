

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
	if (tokenizer->lastread == -2)
	{
		charreader *reader = tokenizer->next_char;
		int result = reader();
		if (result < -128 || result > 127)
			abort();
		tokenizer->lastread = result;
	}
}
