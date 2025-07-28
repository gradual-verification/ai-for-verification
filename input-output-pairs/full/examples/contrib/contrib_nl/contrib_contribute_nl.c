#include "stdlib.h"
#include "threading.h"

struct sum {
    int sum;
};

struct session {
    struct sum *sum_object;
    struct lock *lock;
};


// TODO: make this function pass the verification
/*contribute() function
-params: void *data
-description: takes a session object, frees the session object, acquires the lock, increments the sum field of the sum object by 1, releases the lock. 

It requires the data object is a session with its sum_object and lock, and the current thread is one of the two that can modify sum, 
and the current thread hasn't modified the object. 
It ensures that the current thread has done the contribution on adding the sum.
*/
void contribute(void *data) //@ : thread_run_joinable
{
    struct session *session = data;
    struct lock *lock = session->lock;
    struct sum *sumObject = session->sum_object;
    free(session);
    lock_acquire(lock);
   
        {
            int sum = sumObject->sum;
            sumObject->sum = sum + 1;
        }
        
    lock_release(lock);
}

