#ifndef SOCKETS_H
#define SOCKETS_H

#include <stdbool.h>
#include "stringBuffers.h"

struct server_socket;
struct socket;
struct reader;
struct writer;

/*@
predicate server_socket(struct server_socket *serverSocket);
predicate socket(struct socket *socket, struct reader *reader, struct writer *writer);
predicate reader(struct reader *reader);
predicate writer(struct writer *writer);
@*/

struct server_socket *create_server_socket(int port);
    //@ requires true;
    //@ ensures server_socket(result);
struct socket *server_socket_accept(struct server_socket *serverSocket);
    //@ requires server_socket(serverSocket);
    //@ ensures server_socket(serverSocket) &*& socket(result, ?reader, ?writer) &*& reader(reader) &*& writer(writer);
struct socket *create_client_socket(int port);
    //@ requires true;
    //@ ensures socket(result, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

struct reader *socket_get_reader(struct socket *socket);
    //@ requires socket(socket, ?reader, ?writer);
    //@ ensures socket(socket, reader, writer) &*& result == reader;
struct writer *socket_get_writer(struct socket *socket);
    //@ requires socket(socket, ?reader, ?writer);
    //@ ensures socket(socket, reader, writer) &*& result == writer;
void socket_close(struct socket *socket);
    //@ requires socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);
    //@ ensures true;
    
bool reader_read_line(struct reader *reader, struct string_buffer *buffer);
    //@ requires reader(reader) &*& string_buffer(buffer, _);
    //@ ensures reader(reader) &*& string_buffer(buffer, _);
void writer_write_string(struct writer *writer, char *string);
    //@ requires writer(writer) &*& [?f]string(string, ?cs);
    //@ ensures writer(writer) &*& [f]string(string, cs);
void writer_write_string_buffer(struct writer *writer, struct string_buffer *buffer);
    //@ requires writer(writer) &*& [?f]string_buffer(buffer, ?cs);
    //@ ensures writer(writer) &*& [f]string_buffer(buffer, cs);

#endif
