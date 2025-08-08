
struct tokenizer
{
    charreader*           next_char;
    int                   lastread; // the character lastly read. Special: -1 = EOF, -2 = empty buffer
    int                   lasttoken; // the last token parsed
    struct string_buffer* buffer;
};


typedef int charreader();

struct string_buffer *tokenizer_get_buffer(struct tokenizer *tokenizer)
{
    struct string_buffer *buffer = tokenizer->buffer;
    return buffer;
}
