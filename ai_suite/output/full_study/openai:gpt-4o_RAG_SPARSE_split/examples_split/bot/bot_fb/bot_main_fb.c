#include "sockets.h"

//@ predicate main_inv(struct socket *s, struct reader *r, struct writer *w, struct string_buffer *line, struct string_buffer *nick, struct string_buffer *text) =
//@     socket(s, r, w) &*& reader(r) &*& writer(w) &*& string_buffer(line, _) &*& string_buffer(nick, _) &*& string_buffer(text, _);

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct socket *s = create_client_socket(12345);
    struct reader *r = socket_get_reader(s);
    struct writer *w = socket_get_writer(s);
    bool stop = false;

    struct string_buffer *line = create_string_buffer();
    struct string_buffer *nick = create_string_buffer();
    struct string_buffer *text = create_string_buffer();

    reader_read_line(r, line);
    reader_read_line(r, line);
    writer_write_string(w, "BoT\r\n");
    
    while (!stop)
        //@ invariant main_inv(s, r, w, line, nick, text);
    {
        bool test = true;
        bool result = false;
        
        reader_read_line(r, line);
        result = string_buffer_split(line, " says: ", nick, text);
        test = string_buffer_equals_string(nick, "BoT");
        if (result && !test) {
            test = string_buffer_equals_string(text, "!hello");
            if (test) {
                writer_write_string(w, "Hello ");
                writer_write_string_buffer(w, nick);
                writer_write_string(w, "!\r\n");
            } else {
                test = string_buffer_equals_string(text, "!quit");
                if (test) {
                    writer_write_string(w, "Byebye!\r\n");
                    stop = true;
                    string_buffer_dispose(line);
                    string_buffer_dispose(nick);
                    string_buffer_dispose(text);
                }
            }
        }
    }

    socket_close(s);

    return 0;
}