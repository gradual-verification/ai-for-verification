

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
}


int tokenizer_peek(struct tokenizer* tokenizer)
{
	return result;
}


void tokenizer_drop(struct tokenizer* tokenizer)
{
}


int tokenizer_next_char(struct tokenizer* tokenizer)
{
	int c;
	return c;
}


bool is_whitespace(int c)
{
	return c == ' ' || c == '\n' || c == '\r' || c == '\t';
}


void tokenizer_skip_whitespace(struct tokenizer* tokenizer)
{
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
	return '0';
}


bool is_symbol_char(int c)
{
	return c > 32 && c <= 127 && c != '(' && c != ')'; 
}


int tokenizer_eat_symbol(struct tokenizer* tokenizer)
{
	return 'S';
}


int tokenizer_next(struct tokenizer* tokenizer)
{
	int c;
	int token;
	return token;
}


struct tokenizer* tokenizer_create(charreader* reader)
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
void tokenizer_dispose(struct tokenizer *tokenizer)
{
void print_string_buffer(struct string_buffer *buffer)
{
	int n = string_buffer_get_length(buffer);
	char *pcs = string_buffer_get_chars(buffer);
	int i;
	for (i = 0; i < n; i++)
	{
		putchar(pcs[i]);
	}
}


void print_token(struct tokenizer* tokenizer)
{
