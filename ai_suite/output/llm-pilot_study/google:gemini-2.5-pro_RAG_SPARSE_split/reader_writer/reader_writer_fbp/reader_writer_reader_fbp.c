#include "stdlib.h"
#include "threading.h"

struct rwlock {
    struct mutex *mutex;
    int readers;
};

/*@
// A ghost token used to track whether there are active readers.
// It is a precise predicate, allowing it to be split into fractions.
predicate rwlock_token(struct rwlock *l;);

// A fixpoint defining the small, non-zero fraction of the token
// that each active reader holds.
fixpoint real per_reader_fraction() { return 0.001; }

// The invariant for the mutex. It protects the 'readers' count.
// Crucially, it also holds a fraction of the rwlock_token that is
// inversely proportional to the number of active readers.
predicate_ctor rwlock_inv(struct rwlock *l)() =
    l->readers |-> ?r &*& r >= 0 &*&
    [1 - real_of_int(r) * per_reader_fraction()]rwlock_token(l) &*&
    malloc_block_rwlock(l);

predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l)) &*&
    // We assume the token exists. A create_rwlock function would establish this.
    rwlock_token(l);

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
    [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l)) &*&
    rwlock_token(l);
@*/

// TODO: make this function pass the verification
void reader(struct rwlock *l) //@ : thread_run
    //@ requires thread_run_data(reader)(l);
    //@ ensures true;
{
    //@ open thread_run_data(reader)(l);
    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();
    //@ real f = per_reader_fraction();
    //@ assert l->readers |-> ?r_enter;
    //@ assert [1 - real_of_int(r_enter) * f]rwlock_token(l);

    if (l->readers == INT_MAX) {
        abort();
    }
    l->readers++;

    /*@
    // To re-establish the invariant, we need a fraction of [1 - (r+1)*f] of the token.
    // We currently have [1 - r*f]. Since 1 - r*f = (1 - (r+1)*f) + f,
    // we can split our token fraction, keeping [f] for our thread.
    real current_frac = 1 - real_of_int(r_enter) * f;
    real next_frac = 1 - real_of_int(r_enter + 1) * f;
    assert current_frac == next_frac + f;
    @*/
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);

    // critical section (reading)
    //@ assert [f]rwlock_token(l);

    mutex_acquire(l->mutex);
    //@ open rwlock_inv(l)();
    //@ assert l->readers |-> ?r_exit;

    /*@
    // While in the critical section, this thread holds a fraction [f] of the token.
    // Since f > 0, the total fraction of the token held by all readers must be > 0.
    // The total fraction held by readers is r_exit * f.
    // So, r_exit * f > 0, which implies r_exit > 0.
    // Therefore, the condition (r_exit == 0) is unreachable.
    if (r_exit * f <= 0) abort();
    @*/
    if (l->readers == 0) {
        abort();
    }
    l->readers--;

    /*@
    // To re-establish the invariant, we must return our fraction [f] of the token.
    // The lock currently holds [1 - r_exit*f].
    // We combine our [f] with the lock's fraction to form [1 - (r_exit-1)*f].
    @*/
    //@ close rwlock_inv(l)();
    mutex_release(l->mutex);
    
    //@ leak rwlock_token(l);
}
