#include <stdbool.h>
#include "malloc.h"
#include "lists.h"
#include "stringBuffers.h"
#include "sockets.h"
#include "threading.h"
#include "stdlib.h"
//@ #include "ghostlist.gh"

struct member {
    struct member *next;
    struct string_buffer *nick;
    struct writer *writer;
};

/*@
predicate member(struct member* member) =
    member->nick |-> ?nick &*& [1/2]member->writer |-> ?writer &*& string_buffer(nick, _) &*& writer(writer) &*& malloc_block_member(member);
@*/


/*@
predicate member_weak(struct member* member) =
    member->nick |-> ?nick &*&  &*& string_buffer(nick, _) &*& writer(writer);
@*/

struct room {
    struct member *members;
    //@ int ghost_list_id;
};

/*@
predicate room(struct room* room) =
    room->members |-> ?membersList &*& [?f]room->ghost_list_id |-> ?id &*&
    lseg(membersList, 0, ?members, member) &*&
    ghost_list(id, members) &*& malloc_block_room(room);
@*/


/*@
predicate room_weak(struct room* room) =
    room->members |-> ?membersList  &*&
    lseg(membersList, 0, ?members, member) &*&
    ghost_list(id, members);
@*/

struct room *create_room()
//require true;
 //@ ensures room_weak(result);
 
{
    struct room *room = 0;
    room = malloc(sizeof(struct room));
    if (room == 0) {
        abort();
    }
    room->members = 0;
    //@ close lseg(0, 0, nil, member);
    //@ int i = create_ghost_list();
    //@ room->ghost_list_id = i;
    //@ close room(room);
    return room;
}

bool room_has_member(struct room *room, struct string_buffer *nick)
//@ requires room != NULL && nick != NULL;
//@ ensures hasMember!=NULL;
{
    
    struct member *iter = room->members;
    bool hasMember = false;
   
    while (iter != 0 && !hasMember)
       
    {
       
        hasMember = string_buffer_equals(iter->nick, nick);
        
        iter = *(void **)(void *)iter;
       
    }
   
    return hasMember;
}
/**
 * Description:
 * The room_broadcast_message function broadcasts a message to all members of the specified room. 
 It iterates through the linked list of members associated with the room and sends the provided message to each member's writer.
  A newline character is appended to the message to ensure proper formatting. The function assumes that the room and its members have been properly initialized.
 *
 * @param room A pointer to the room structure.
 * @param message A pointer to the string buffer containing the message to be broadcasted.
 */
void room_broadcast_message(struct room *room, struct string_buffer *message)
    //@ requires room != NULL &*& message != NULL&*& room->members>=0;
    //@ ensures true;
{
    //@ open room(room);
    struct member *iter = room->members;
   
    while (iter != 0)
        
    {
        
        writer_write_string_buffer(iter->writer, message);
        writer_write_string(iter->writer, "\r\n");
   
        iter = *(void **)(void *)iter;
     
    }
  
}

struct session {
    struct room *room;
    struct lock *room_lock;
    struct socket *socket;
};

/*@

predicate_ctor room_ctor(struct room *room)() =
    room(room);

predicate session(struct session *session) =
    session->room |-> ?room &*& session->room_lock |-> ?roomLock &*& session->socket |-> ?socket &*& malloc_block_session(session)
        &*& [_]lock(roomLock, _, room_ctor(room)) &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

@*/


/*@



predicate session_functional_behavior(struct session *session) =
    session->room |-> ?room &*& session->room_lock |-> ?roomLock &*& session->socket |-> ?socket  &*& socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

@*/

/**
 * Description:
 * The create_session function creates and initializes a new session structure. It allocates memory for the session, sets its room, room lock, and socket members, and returns a pointer to the newly created session.
 *
 * @param room A pointer to the room structure. It must not be null.
 * @param roomLock A pointer to the lock for synchronizing access to the room. It must not be null.
 * @param socket A pointer to the socket used for communication. It must not be null.
 * @return A pointer to the newly created session. The returned pointer is guaranteed to be non-null.
 *

 */

struct session *create_session(struct room *room, struct lock *roomLock, struct socket *socket)
 //@ socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);
    //@ ensures session_functional_behavior(result);
{
    struct session *session = malloc(sizeof(struct session));
    if (session == 0) {
        abort();
    }
    session->room = room;
    session->room_lock = roomLock;
    session->socket = socket;
    
    return session;
}
/**
 * Description:
 * The session_run_with_nick function manages the interaction of a member within a chat room. It handles the member joining the room, broadcasting messages, and eventually leaving the room. It ensures thread-safe operations through the use of locks.
 *
 * @param room A pointer to the room structure where the session takes place. It must not be null.
 * @param roomLock A pointer to the lock used for synchronizing access to the room. It must not be null.
 * @param reader A pointer to the reader used for receiving messages from the member. It must not be null.
 * @param writer A pointer to the writer used for sending messages to the member. It must not be null.
 * @param nick A pointer to the string buffer containing the member's nickname. It must not be null.
 *
 * @requires room != NULL && roomLock != NULL && reader != NULL && writer != NULL && nick != NULL;
 * @ensures true;
 */
void session_run_with_nick(struct room *room, struct lock *roomLock, struct reader *reader, struct writer *writer, struct string_buffer *nick)
   /*@
    requires
        locked(roomLock, ?roomLockId, room_ctor(room), currentThread, _) &*& lockset(currentThread, cons(roomLockId, nil)) &*&
        room(room) &*& reader(reader) &*& writer(writer) &*& string_buffer(nick, _);
    @*/
    /*@
    ensures
        lockset(currentThread, nil) &*&
        reader(reader) &*& writer(writer) &*& string_buffer(nick, _);
    @*/
{
    struct member *member = 0;

    struct string_buffer *joinMessage = create_string_buffer();
    string_buffer_append_string_buffer(joinMessage, nick);
    string_buffer_append_string(joinMessage, " has joined the room.");
    room_broadcast_message(room, joinMessage);
    string_buffer_dispose(joinMessage);

    {
        struct string_buffer *nickCopy = string_buffer_copy(nick);
        
        member = malloc(sizeof(struct member));
        if (member == 0) {
            abort();
        }
        member->nick = nickCopy;
        member->writer = writer;
        
        member->next = room->members;
        room->members = member;
      
    }
    

    lock_release(roomLock);

    
    {
        bool eof = false;
        struct string_buffer *message = create_string_buffer();
        while (!eof)
            
        {
            eof = reader_read_line(reader, message);
            if (eof) {
            } else {
                lock_acquire(roomLock);
             
                {
                    struct string_buffer *fullMessage = create_string_buffer();
                    string_buffer_append_string_buffer(fullMessage, nick);
                    string_buffer_append_string(fullMessage, " says: ");
                    string_buffer_append_string_buffer(fullMessage, message);
                    room_broadcast_message(room, fullMessage);
                    string_buffer_dispose(fullMessage);
                }
               
                lock_release(roomLock);
            }
        }
        string_buffer_dispose(message);
    }
    
    lock_acquire(roomLock);
   
    {
        struct member *membersList = room->members;
    
        lseg_remove(&room->members, member);
      
    }
  
    {
        struct string_buffer *goodbyeMessage = create_string_buffer();
        string_buffer_append_string_buffer(goodbyeMessage, nick);
        string_buffer_append_string(goodbyeMessage, " left the room.");
        room_broadcast_message(room, goodbyeMessage);
        string_buffer_dispose(goodbyeMessage);
    }
   
    lock_release(roomLock);
    
  ;
    string_buffer_dispose(member->nick);
    free(member);
}

/*@

predicate_family_instance thread_run_data(session_run)(void *data) = session(data);

@*/



void session_run(void *data) //@ : thread_run
   //@ requires thread_run_data(session_run)(data) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
  
{

    struct session *session = data;

    struct room *room = session->room;
    struct lock *roomLock = session->room_lock;
    struct socket *socket = session->socket;
    struct writer *writer = socket_get_writer(socket);
    struct reader *reader = socket_get_reader(socket);
    free(session);
    
    writer_write_string(writer, "Welcome to the chat room.\r\n");
    writer_write_string(writer, "The following members are present:\r\n");
    
    lock_acquire(roomLock);
  
    {
        struct member *iter = room->members;
       
        while (iter != 0)
            
        {
            
            writer_write_string_buffer(writer, iter->nick);
            writer_write_string(writer, "\r\n");
            
            iter = *(void **)(void *)iter;
           
        }
        
    }

    lock_release(roomLock);

    {
        struct string_buffer *nick = create_string_buffer();
        bool done = false;
        while (!done)
         
        {
            writer_write_string(writer, "Please enter your nick: ");
            {
                bool eof = reader_read_line(reader, nick);
                if (eof) {
                    done = true;
                } else {
                    lock_acquire(roomLock);
               
                    {
                        bool hasMember = room_has_member(room, nick);
                        if (hasMember) {
                       
                            lock_release(roomLock);
                            writer_write_string(writer, "Error: This nick is already in use.\r\n");
                        } else {
                            session_run_with_nick(room, roomLock, reader, writer, nick);
                            done = true;
                        }
                    }
                }
            }
        }
        string_buffer_dispose(nick);
    }

    socket_close(socket);
}

int main() //@ : main
    //@ requires true;
    //@ ensures false;
{
    struct room *room = create_room();
    
    struct lock *roomLock = create_lock();

    struct server_socket *serverSocket = create_server_socket(12345);

    for (;;)
     
    {
        struct socket *socket = server_socket_accept(serverSocket);
        struct session *session = create_session(room, roomLock, socket);
 
        thread_start(session_run, session);
    }
}
