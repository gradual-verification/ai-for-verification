#include "stdlib.h"
#include "threading.h"

/*@
predicate_ctor rwlock_inv(struct rwlock *l)() =
  l->readers |-> ?r &*& r >= 0 &*& malloc_block_rwlock(l);

predicate_family_instance thread_run_data(reader)(struct rwlock *l) =
  [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));

predicate_family_instance thread_run_data(writer)(struct rwlock *l) =
  [1/2]l->mutex |-> ?m &*& [1/2]mutex(m, rwlock_inv(l));
@*/

struct rwlock {
  struct mutex *mutex;
  int readers;
};

/*@
lemma_auto void create_mutex_ghost_arg_rwl(predicate() p);
@*/

struct rwlock *rwlock_init()
/*@
  requires true;
  ensures result->mutex |-> ?m &*& mutex(m, rwlock_inv(result));
@*/
{
  struct rwlock *l = malloc(sizeof(struct rwlock));
  if (l == 0) abort();
  l->readers = 0;
  l->mutex = create_mutex();
  /*@
  close rwlock_inv(l)();
  close create_mutex_ghost_arg_rwl(rwlock_inv(l));
  @*/
  return l;
}