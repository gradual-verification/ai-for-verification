#include "sockets.h"


// TODO: make this function pass the verification
/***
 * Description:
 * This program establishes a client socket connection to a server on port `12345`, 
 * and continuously listens for incoming messages and processes specific bot commands.
 *
 * The program utilizes string buffers to handle message parsing and output formatting.
 */
int main()
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
