#include "stdlib.h"
#include "threading.h"

struct sum {
    int sum;
};

struct session {
    struct sum *sum_object;
    struct lock *lock;
};

/*contrinute() function
-params: void *data
-description: This function increments the sum by 1. 
It acquires the lock, increments the sum by 1 and 
then releases the lock.
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

/*main() function
-params: None
-description: This function creates a sum object and a lock object. It then creates two sessions, each with a sum object and a lock object. It then creates two threads, each with a session object. The first thread increments the sum by 1 and the second thread increments the sum by 1. The main function then joins the first thread and the second thread. The lock object is then disposed. The sum is then checked to be 2.
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
    
    // The following perform_action statement is only to show contrib_handle(_, box1, 1)
    
    int sum = sumObject->sum;
    assert(sum == 2);
    free(sumObject);

    return 0;
}