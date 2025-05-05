#include <stdlib.h>
#include <threading.h>

struct MutexCell<T> {
  mutex mutex;
  T payload;
};

/***
 * Description: 
The create_MutexCell function allocates and initializes a new MutexCell object with the given value with generic type T.

@param value - The value to initialize the payload field of the struct, which satisfies the property of T
@return - A pointer to the newly allocated MutexCell object, whose mutex is not held and payload satisfies the property of T

The function ensures that the return value is a MutexCell
*/
struct MutexCell<T> *create_MutexCell<T>(T value)
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
{
    mutex_release(mutexCell->mutex);
}
