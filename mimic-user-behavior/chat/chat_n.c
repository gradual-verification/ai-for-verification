#include <stdbool.h>

#include "malloc.h"

#include "lists.h"

#include "stringBuffers.h"

#include "sockets.h"

#include "threading.h"

#include "stdlib.h"
 //@ #include "ghostlist.gh"

struct member {
  struct member * next;
  struct string_buffer * nick;
  struct writer * writer;
};

/*@
predicate member(struct member* member) =
    member->nick |-> ?nick &*& [1/2]member->writer |-> ?writer &*& string_buffer(nick, _) &*& writer(writer) &*& malloc_block_member(member);
@*/

struct room {
  struct member * members;
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
struct room * create_room()
{
  struct room * room = 0;
  room = malloc(sizeof(struct room));
  if (room == 0) {
    abort();
  }
  room -> members = 0;

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
bool room_has_member(struct room * room, struct string_buffer * nick)
{

  struct member * iter = room -> members;
  bool hasMember = false;

  while (iter != 0 && !hasMember)

  {

    hasMember = string_buffer_equals(iter -> nick, nick);
   
    iter = * (void ** )(void * ) iter;
   
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
void room_broadcast_message(struct room * room, struct string_buffer * message)
{
 
  struct member * iter = room -> members;
 
  while (iter != 0)

  {

    writer_write_string_buffer(iter -> writer, message);
    writer_write_string(iter -> writer, "\r\n");
  
    iter = * (void ** )(void * ) iter;
 
  }

}

struct session {
  struct room * room;
  struct lock * room_lock;
  struct socket * socket;
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
 * The create_session function creates a new session object. 
 It allocates memory for the session structure, 
 initializes its members with the provided room, lock, and socket, and returns a pointer to the newly created session. 
 If memory allocation fails, the program aborts to prevent further execution with an invalid pointer.
 *
 * @param room A pointer to the room structure associated with the session.
 * @param roomLock A pointer to the lock for synchronizing access to the room.
 * @param socket A pointer to the socket used for communication in the session.
 *
 * @return A pointer to the newly created session structure.
 */

struct session * create_session(struct room * room, struct lock * roomLock, struct socket * socket) {
  struct session * session = malloc(sizeof(struct session));
  if (session == 0) {
    abort();
  }
  session -> room = room;
  session -> room_lock = roomLock;
  session -> socket = socket;

  return session;
}
/**
 * Description:
 * The session_run_with_nick function manages a session for a user identified by a nickname. 
 It handles joining and leaving the room, broadcasting messages to all members, and reading messages from the user.
 * 
 * @param room A pointer to the room structure.
 * @param roomLock A pointer to the lock for synchronizing access to the room.
 * @param reader A pointer to the reader for input.
 * @param writer A pointer to the writer for output.
 * @param nick A pointer to the string buffer containing the user's nickname.
 */
void session_run_with_nick(struct room * room, struct lock * roomLock, struct reader * reader, struct writer * writer, struct string_buffer * nick)
{
  struct member * member = 0;

  struct string_buffer * joinMessage = create_string_buffer();
  string_buffer_append_string_buffer(joinMessage, nick);
  string_buffer_append_string(joinMessage, " has joined the room.");
  room_broadcast_message(room, joinMessage);
  string_buffer_dispose(joinMessage);

  {
    struct string_buffer * nickCopy = string_buffer_copy(nick);
   
    member = malloc(sizeof(struct member));
    if (member == 0) {
      abort();
    }
    member -> nick = nickCopy;
    member -> writer = writer;

    member -> next = room -> members;
    room -> members = member;

  }

  
  lock_release(roomLock);
  

  {
    bool eof = false;
    struct string_buffer * message = create_string_buffer();
    while (!eof)
   
    {
      eof = reader_read_line(reader, message);
      if (eof) {} else {
        lock_acquire(roomLock);
       
        {
          struct string_buffer * fullMessage = create_string_buffer();
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
    struct member * membersList = room -> members;
  
    lseg_remove( & room -> members, member);

  }

  {
    struct string_buffer * goodbyeMessage = create_string_buffer();
    string_buffer_append_string_buffer(goodbyeMessage, nick);
    string_buffer_append_string(goodbyeMessage, " left the room.");
    room_broadcast_message(room, goodbyeMessage);
    string_buffer_dispose(goodbyeMessage);
  }

  lock_release(roomLock);

  string_buffer_dispose(member -> nick);
  free(member);
}

/*@

predicate_family_instance thread_run_data(session_run)(void *data) = session(data);

@*/

/**
 * Description:
 * The session_run function manages the main logic for a chat session. It initializes the session by setting up the room, lock, and socket. It then welcomes the user, lists current room members, and prompts the user to enter a nickname. If the nickname is already taken, the user is prompted to enter a different one. Once a valid nickname is provided, the function hands off control to session_run_with_nick to manage the user's interaction within the room. After the session ends, it closes the socket.
 *
 * @param data A pointer to the session structure containing the room, lock, and socket information.
 */

void session_run(void * data) //@ : thread_run
{

  struct session * session = data;

  struct room * room = session -> room;
  struct lock * roomLock = session -> room_lock;
  struct socket * socket = session -> socket;
  struct writer * writer = socket_get_writer(socket);
  struct reader * reader = socket_get_reader(socket);
  free(session);

  writer_write_string(writer, "Welcome to the chat room.\r\n");
  writer_write_string(writer, "The following members are present:\r\n");

  lock_acquire(roomLock);

  {
    struct member * iter = room -> members;

    while (iter != 0)

    {
 
      writer_write_string_buffer(writer, iter -> nick);
      writer_write_string(writer, "\r\n");
      
      iter = * (void ** )(void * ) iter;
    
    }
   
  }

  lock_release(roomLock);

  {
    struct string_buffer * nick = create_string_buffer();
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
{
  struct room * room = create_room();
 
  struct lock * roomLock = create_lock();

  struct server_socket * serverSocket = create_server_socket(12345);

  for (;;)
  
  {
    struct socket * socket = server_socket_accept(serverSocket);
    struct session * session = create_session(room, roomLock, socket);
   
    thread_start(session_run, session);
  }
}