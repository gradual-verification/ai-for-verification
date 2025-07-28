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
