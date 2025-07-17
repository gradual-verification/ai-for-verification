#include "stdlib.h"
#include "threading.h"

/* A very small read–write lock implemented on top of a mutex.
   Only an initialisation function is provided here; further
   operations (acquire-read, acquire-write, …) could be added
   in the same style. */

struct rwlock {
    struct mutex *mutex;   /* protects ‘readers’                   */
    int            readers;/* number of current readers (>= 0)     */
};

/*-------------------------------------------------------------*/
/* Invariant owned by the mutex that lives inside the rwlock.  */
/* The invariant only transfers ownership of the ‘readers’     */
/* field (and the malloc block it lives in); the ‘mutex’       */
/* field itself stays outside the invariant, so the creator    */
/* of the rwlock keeps direct access to it.                    */
/*-------------------------------------------------------------*/
/*@ predicate_ctor rwlock_inv(struct rwlock *l)() =
      l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);
@*/

/*-------------------------------------------------------------*/
/* rwlock_init : allocate and initialise a read–write lock.    */
/*-------------------------------------------------------------*/
struct rwlock *rwlock_init()
    //@ requires true;
    //@ ensures  result->mutex |-> ?m &*& mutex(m, rwlock_inv(result));
{
    /* allocate the rwlock structure */
    struct rwlock *l = malloc(sizeof(struct rwlock));
    if (l == 0) abort();                  /* allocation failed   */

    /* initialise both fields                                     */
    l->mutex   = 0;                       /* produce points-to   */
    l->readers = 0;                       /* produce points-to   */

    /* hand the ‘readers’ field (and the malloc block) to the
       mutex that we are about to create:                       */
    //@ close rwlock_inv(l)();                       // p()
    //@ close create_mutex_ghost_arg(rwlock_inv(l)); // ghost arg
    struct mutex *m = create_mutex();                /* p() is   */
                                                     /* consumed */

    /* store the freshly created mutex pointer in the structure   */
    l->mutex = m;     /* we still own the mutex field, so we can
                         update it safely                        */

    /* The post-condition is trivially satisfied now:
         – we still own   l->mutex |-> m
         – create_mutex gave us mutex(m, rwlock_inv(l))           */
    return l;
}