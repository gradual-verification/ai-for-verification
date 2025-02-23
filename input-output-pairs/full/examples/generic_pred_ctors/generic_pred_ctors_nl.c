#include <stdlib.h>
#include <threading.h>

struct MutexCell<T> {
  mutex mutex;
  T payload;
};

/*@

predicate_ctor MutexCell_inv<T>(struct MutexCell<T> *mutexCell, predicate(T) T_own)() =
    mutexCell->payload |-> ?payload &*& T_own(payload);

predicate MutexCell<T>(struct MutexCell<T> *mutexCell, predicate(T) T_own;) =
    mutexCell->mutex |-> ?mutex &*&
    mutex(mutex, (MutexCell_inv)(mutexCell, T_own));

predicate MutexCell_held<T>(struct MutexCell<T> *mutexCell, predicate(T) T_own, int thread_id, real q) =
    [q]mutexCell->mutex |-> ?mutex &*&
    mutex_held(mutex, MutexCell_inv<T>(mutexCell, T_own), thread_id, q);

@*/

/***
 * Description: 
The create_MutexCell function allocates and initializes a new MutexCell object with the given value with generic type T.

@param value - The value to initialize the payload field of the struct, which satisfies the property of T
@return - A pointer to the newly allocated MutexCell object, whose mutex is not held and payload satisfies the property of T

The function ensures that the allocated memory block for the MutexCell object is valid.
If memory allocation fails, the program aborts.
*/
struct MutexCell<T> *create_MutexCell<T>(T value)
//@ requires exists<predicate(T)>(?T_own) &*& (T_own)(value);
//@ ensures MutexCell<T>(result, T_own);
{
    struct MutexCell<T> *result = malloc(sizeof(struct MutexCell<T>));
    if (result == 0) abort();
    result->payload = value;
    mutex mutex = create_mutex();
    result->mutex = mutex;
    return result;
}

/***
 * Description: 
The MutexCell_acquire function acquires the mutex lock for the given mutexCell with generic type T .

@param mutexCell - The MutexCell object whose mutex is not held

The function ensures that the mutex of mutexCell is held and the property of payload is not changed after the execution
*/
void MutexCell_acquire<T>(struct MutexCell<T> *mutexCell)
//@ requires [?q]MutexCell<T>(mutexCell, ?T_own);
//@ ensures MutexCell_held<T>(mutexCell, T_own, currentThread, q) &*& mutexCell->payload |-> ?payload &*& T_own(payload);
{
    mutex_acquire(mutexCell->mutex);
}

/***
 * Description: 
The MutexCell_release function releases the mutex lock for the given mutexCell with generic type T .

@param mutexCell - The MutexCell object whose mutex is held

The function ensures that the mutex of mutexCell is unheld and the property of payload is not changed after the execution
*/
void MutexCell_release<T>(struct MutexCell<T> *mutexCell)
//@ requires MutexCell_held<T>(mutexCell, ?T_own, currentThread, ?q) &*& mutexCell->payload |-> ?payload &*& T_own(payload);
//@ ensures [q]MutexCell<T>(mutexCell, T_own);
{
    mutex_release(mutexCell->mutex);
}
