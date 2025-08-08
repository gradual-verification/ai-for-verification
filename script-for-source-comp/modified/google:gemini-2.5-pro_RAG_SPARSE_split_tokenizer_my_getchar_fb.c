    typedef int charreader();
    int getchar();


struct tokenizer
{
	charreader*           next_char;
	int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
	int                   lasttoken; // the last token parsed
	struct string_buffer* buffer;
};



typedef int charreader();


int my_getchar() //@ : charreader
{
	return getchar();
}
