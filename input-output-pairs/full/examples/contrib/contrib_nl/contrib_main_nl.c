#include "stdlib.h"
#include "threading.h"

struct sum {
    int sum;
};

struct session {
    struct sum *sum_object;
    struct lock *lock;
};


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


// TODO: make this function pass the verification
/*main() function
-params: none
-description: creates a sum object and a lock object, creates two sessions with the sum object and lock object, creates two threads with the contribute function and the two sessions, joins the first thread, joins the second thread, disposes the lock object, checks if the sum object's sum field is 2, frees the sum object
*/
int main()
{
    struct sum *sumObject = malloc(sizeof(struct sum));
    if (sumObject == 0) {
        abort();
    }
    sumObject->sum = 0;
    struct lock *lock = create_lock();
    
    struct session *session1 = malloc(sizeof(struct session));
    if (session1 == 0) {
        abort();
    }
    session1->sum_object = sumObject;
    session1->lock = lock;
    struct thread *thread1 = thread_start_joinable(contribute, session1);
    
    struct session *session2 = malloc(sizeof(struct session));
    if (session2 == 0) {
        abort();
    }
    session2->sum_object = sumObject;
    session2->lock = lock;
    struct thread *thread2 = thread_start_joinable(contribute, session2);
    
    thread_join(thread1);
    
    thread_join(thread2);
    
    lock_dispose(lock);
    
    int sum = sumObject->sum;
    assert(sum == 2);
    free(sumObject);

    return 0;
}
