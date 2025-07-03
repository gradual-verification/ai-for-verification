#include "stdlib.h"
#include "threading.h"

/* =========================================================================
   Data structure and invariants
   ====================================================================== */

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r                    /* the protected data              */
    &*& r >= 0                           /* non-negative reader counter      */
    &*& malloc_block_rwlock(l);          /* memory ownership                 */

predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    /* each thread gets half of the pointer to the mutex and half of the
       mutex chunk – enough to acquire/release it                         */
    [1/2]l->mutex |-> ?m
  &*& [1/2]mutex(m, rwlock_inv(l));

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m
  &*& [1/2]mutex(m, rwlock_inv(l));
@*/

/* =========================================================================
   Verified reader function
   ====================================================================== */

// TODO: make this function pass the verification
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    /* ----------------- enter critical section ----------------- */
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();                 /* gain access to shared state  */
    //@ integer_limits(&(l->readers));        /* obtain INT_MIN/INT_MAX facts */
    int r = l->readers;

    if (l->readers == INT_MAX) {
        /* overflow would occur; abort is allowed */
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
        abort();
    }
    //@ assert r < INT_MAX;                  /* proof obligation for overflow */
    l->readers = r + 1;                      /* safe increment               */
    //@ close rwlock_inv(l)();               /* restore invariant             */
    mutex_release(l->mutex);
    /* --------------- leave critical section ------------------- */

    /* ------------ perform (read-only) user work --------------- */
    // ... (omitted) ...

    /* ------------- exit phase: decrement counter -------------- */
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();
    //@ integer_limits(&(l->readers));
    r = l->readers;

    if (l->readers == 0) {
        /* counter underflow would occur */
        //@ close rwlock_inv(l)();
        mutex_release(l->mutex);
        abort();
    }
    //@ assert r > 0;                        /* ensures r-1 is still non-neg. */
    l->readers = r - 1;                      /* safe decrement               */
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
    /* ----------------------------------------------------------- */
}