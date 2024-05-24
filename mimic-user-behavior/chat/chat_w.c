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
/**
 * Description:
 * This function is responsible for creating a new room object. It allocates memory for the room structure, initializes its members, and returns a pointer to the newly created room.
 *
 * Initially, the `room` pointer is set to `0` (NULL) to ensure it points to no valid memory address. The function then attempts to allocate memory for a `struct room`. If the memory allocation fails and `room` remains `0` (NULL), the program aborts to prevent further execution with an invalid pointer.
 *
 * The `room->members` is initialized to `0`, indicating that the room currently has no members.
 *
 * The function also includes ghost code for verification purposes, ensuring the integrity of the room structure.
 *
 * @return A pointer to the newly created room structure.
 */
struct room *create_room()
//require true;
//ensure room!=NULL&*& room->members>=0;
 
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
/**
 * Description:
 * The room_has_member function checks if a given room contains a member with the specified nickname. 
 It iterates through the linked list of members associated with the room, comparing each member's nickname with the provided nickname 
 until a match is found or the end of the list is reached. If a member with the same nickname is found, 
 the function returns true; otherwise, it returns false. The function assumes that the room and its members have been properly initialized. 
 *
 * @param room A pointer to the room structure.
 * @param nick A pointer to the string buffer containing the nickname to search for.
 *
 * @return True if a member with the specified nickname is found in the room, otherwise false.
 */
bool room_has_member(struct room *room, struct string_buffer *nick)
//@ requires room != NULL && nick != NULL;
//@ ensures hasMember!=NULL;
{
    //@ open room(room);
    //@ struct member *membersList = room->members;
    //@ assert lseg(membersList, 0, ?members, member);
    struct member *iter = room->members;
    bool hasMember = false;
    //@ close lseg(membersList, membersList, nil, member);
    while (iter != 0 && !hasMember)
        /*@
        invariant
            string_buffer(nick, _) &*&
            lseg(membersList, iter, ?members0, member) &*& lseg(iter, 0, ?members1, member) &*& members == append(members0, members1);
        @*/
    {
        //@ open lseg(iter, 0, members1, member);
        //@ open member(iter);
        hasMember = string_buffer_equals(iter->nick, nick);
        //@ close member(iter);
        iter = *(void **)(void *)iter;
        //@ lseg_add(membersList);
    }
    //@ lseg_append_final(membersList);
    //@ close room(room);
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
    //@ assert lseg(?list, 0, ?ms, member);
    //@ close lseg(list, list, nil, member);
    while (iter != 0)
        //@ invariant string_buffer(message, _) &*& lseg(list, iter, ?ms0, member) &*& lseg(iter, 0, ?ms1, member) &*& ms == append(ms0, ms1);
    {
        //@ open lseg(iter, 0, ms1, member);
        //@ open member(iter);
        writer_write_string_buffer(iter->writer, message);
        writer_write_string(iter->writer, "\r\n");
        //@ close member(iter);
        iter = *(void **)(void *)iter;
        //@ lseg_add(list);
    }
    //@ lseg_append_final(list);
    //@ close room(room);
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
   //@ requires room != NULL && roomLock != NULL && socket != NULL;
//@ ensures session != NULL;
{
    struct session *session = malloc(sizeof(struct session));
    if (session == 0) {
        abort();
    }
    session->room = room;
    session->room_lock = roomLock;
    session->socket = socket;
    //@ close session(session);
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
 //@ requires room != NULL && roomLock != NULL && reader != NULL && writer != NULL && nick != NULL;
//@ ensures true;
{
    struct member *member = 0;

    struct string_buffer *joinMessage = create_string_buffer();
    string_buffer_append_string_buffer(joinMessage, nick);
    string_buffer_append_string(joinMessage, " has joined the room.");
    room_broadcast_message(room, joinMessage);
    string_buffer_dispose(joinMessage);

    {
        struct string_buffer *nickCopy = string_buffer_copy(nick);
        //@ open room(room);
        member = malloc(sizeof(struct member));
        if (member == 0) {
            abort();
        }
        member->nick = nickCopy;
        member->writer = writer;
        //@ split_fraction member_writer(member, _) by 1/2;
        //@ close member(member);
        //@ assert room->members |-> ?list &*& lseg(list, 0, ?members, @member);
        member->next = room->members;
        room->members = member;
        //@ open member_next(member, _);
        //@ close lseg(member, 0, cons(member, members), @member);
        //@ assert [_]room->ghost_list_id |-> ?id;
        //@ split_fraction room_ghost_list_id(room, id);
        //@ ghost_list_add(id, member);
        //@ close room(room);
    }
    
    //@ close room_ctor(room)();
    lock_release(roomLock);
    //@ leak [_]lock(roomLock, roomLockId, room_ctor(room));
    
    {
        bool eof = false;
        struct string_buffer *message = create_string_buffer();
        while (!eof)
            //@ invariant reader(reader) &*& string_buffer(nick, _) &*& string_buffer(message, _) &*& [_]lock(roomLock, roomLockId, room_ctor(room)) &*& lockset(currentThread, nil);
        {
            eof = reader_read_line(reader, message);
            if (eof) {
            } else {
                lock_acquire(roomLock);
                //@ open room_ctor(room)();
                {
                    struct string_buffer *fullMessage = create_string_buffer();
                    string_buffer_append_string_buffer(fullMessage, nick);
                    string_buffer_append_string(fullMessage, " says: ");
                    string_buffer_append_string_buffer(fullMessage, message);
                    room_broadcast_message(room, fullMessage);
                    string_buffer_dispose(fullMessage);
                }
                //@ close room_ctor(room)();
                lock_release(roomLock);
            }
        }
        string_buffer_dispose(message);
    }
    
    lock_acquire(roomLock);
    //@ open room_ctor(room)();
    //@ open room(room);
    {
        struct member *membersList = room->members;
        //@ open room_members(room, _);
        //@ assert lseg(membersList, 0, ?members, @member);
        //@ assert [_]ghost_list_member_handle(?id, ?d);
        //@ ghost_list_member_handle_lemma(id, d);
        lseg_remove(&room->members, member);
        //@ assert pointer(&room->members, ?list);
        //@ close room_members(room, list);
        //@ assert pointer((void *)member, ?memberNext);
        //@ close member_next(member, memberNext);
    }
    //@ assert ghost_list(?id, _);
    //@ ghost_list_remove(id, member);
    //@ close room(room);
    {
        struct string_buffer *goodbyeMessage = create_string_buffer();
        string_buffer_append_string_buffer(goodbyeMessage, nick);
        string_buffer_append_string(goodbyeMessage, " left the room.");
        room_broadcast_message(room, goodbyeMessage);
        string_buffer_dispose(goodbyeMessage);
    }
    //@ close room_ctor(room)();
    lock_release(roomLock);
    
    //@ open member(member);
    string_buffer_dispose(member->nick);
    free(member);
}

/*@

predicate_family_instance thread_run_data(session_run)(void *data) = session(data);

@*/

/**
 * Description:
 * The session_run function initializes and manages a user session within a chat room. 
 It handles welcoming the user, displaying the list of current members, and prompting the user to enter their nickname.
  It ensures thread-safe operations through the use of locks.
 *
 * @param data A pointer to the session data structure. It must not be null.
 *
 * @requires data != NULL;
 * @ensures true;
 */

void session_run(void *data) //@ : thread_run
//@ requires data != NULL;
//@ ensures true;
  
{
    //@ open thread_run_data(session_run)(data);
    struct session *session = data;
    //@ open session(session);
    struct room *room = session->room;
    struct lock *roomLock = session->room_lock;
    struct socket *socket = session->socket;
    struct writer *writer = socket_get_writer(socket);
    struct reader *reader = socket_get_reader(socket);
    free(session);
    
    writer_write_string(writer, "Welcome to the chat room.\r\n");
    writer_write_string(writer, "The following members are present:\r\n");
    
    lock_acquire(roomLock);
    //@ open room_ctor(room)();
    //@ open room(room);
    {
        struct member *iter = room->members;
        //@ assert lseg(?membersList, 0, ?ms, member);
        //@ close lseg(membersList, membersList, nil, member);
        while (iter != 0)
            //@ invariant writer(writer) &*& lseg(membersList, iter, ?ms0, member) &*& lseg(iter, 0, ?ms1, member) &*& ms == append(ms0, ms1);
        {
            //@ open lseg(iter, 0, ms1, member);
            //@ open member(iter);
            writer_write_string_buffer(writer, iter->nick);
            writer_write_string(writer, "\r\n");
            //@ close member(iter);
            iter = *(void **)(void *)iter;
            //@ lseg_add(membersList);
        }
        //@ lseg_append_final(membersList);
    }
    //@ close room(room);
    //@ close room_ctor(room)();
    lock_release(roomLock);

    {
        struct string_buffer *nick = create_string_buffer();
        bool done = false;
        while (!done)
          //@ invariant writer(writer) &*& reader(reader) &*& string_buffer(nick, _) &*& [_]lock(roomLock, _, room_ctor(room)) &*& lockset(currentThread, nil);
        {
            writer_write_string(writer, "Please enter your nick: ");
            {
                bool eof = reader_read_line(reader, nick);
                if (eof) {
                    done = true;
                } else {
                    lock_acquire(roomLock);
                    //@ open room_ctor(room)();
                    {
                        bool hasMember = room_has_member(room, nick);
                        if (hasMember) {
                            //@ close room_ctor(room)();
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
    //@ close room_ctor(room)();
    //@ close create_lock_ghost_args(room_ctor(room), nil, nil);
    struct lock *roomLock = create_lock();
    //@ leak lock(roomLock, _, _);
    struct server_socket *serverSocket = create_server_socket(12345);

    for (;;)
        //@ invariant [_]lock(roomLock, _, room_ctor(room)) &*& server_socket(serverSocket);
    {
        struct socket *socket = server_socket_accept(serverSocket);
        struct session *session = create_session(room, roomLock, socket);
        //@ close thread_run_data(session_run)(session);
        thread_start(session_run, session);
    }
}
