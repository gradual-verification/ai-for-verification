/*@
inductive trace = zero | inc(int, trace) | dec(int, trace) | cas_(int, int, int, trace);

fixpoint bool is_good_prefix(trace pref, trace trace, int ctid) {
  switch(trace) {
    case zero: return pref == zero;
    case inc(tid, trace0): return pref == trace || (tid != ctid && is_good_prefix(pref, trace0, ctid));
    case dec(tid, trace0): return pref == trace || (tid != ctid && is_good_prefix(pref, trace0, ctid));
    case cas_(tid, old, new, trace0): return pref == trace || (tid != ctid && is_good_prefix(pref, trace0, ctid));
  }
}

fixpoint int execute_trace(trace trace) {
  switch(trace) {
    case zero: return 0;
    case inc(tid, trace0): return execute_trace(trace0) + 1;
    case dec(tid, trace0): return execute_trace(trace0) - 1;
    case cas_(tid, old, new, trace0): return execute_trace(trace0) == old ? new : execute_trace(trace0);
  }
}

predicate cell(int* c, fixpoint(trace, bool) allowed);

predicate last_seen(int* c, int tid, trace trace);


lemma void last_seen_allowed(int* c, int ctid);
  requires [?f]cell(c, ?allowed) &*& last_seen(c, ctid, ?trace);
  ensures [f]cell(c, allowed) &*& last_seen(c, ctid, trace) &*& allowed(trace) == true;
@*/

/*@
typedef lemma void dec_allowed(trace pretrace, fixpoint(trace, bool) allowed, int ctid)(trace trace);
  requires is_good_prefix(pretrace, trace, ctid) == true &*& allowed(trace) == true;
  ensures allowed(dec(ctid, trace)) == true;
@*/

/*@
typedef lemma void cas_allowed(trace pretrace, fixpoint(trace, bool) allowed, int old, int new)(trace trace);
  requires is_good_prefix(pretrace, trace, currentThread) == true &*& allowed(trace) == true;
  ensures allowed(cas_(currentThread, old, new, trace)) == true;
@*/


/*@
fixpoint bool incr_only(trace trace) {
  switch(trace) {
    case zero: return true;
    case inc(tid, trace0): return incr_only(trace0);
    case dec(tid, trace0): return false;
    case cas_(tid, old, new, trace0): return old <= new && incr_only(trace0);
  }
}
@*/


/*@
fixpoint option<int> lock_owner(trace trace) {
  switch(trace) {
    case zero: return none;
    case inc(tid, trace0): return none;
    case dec(tid, trace0): return none;
    case cas_(tid, old, new, trace0): return execute_trace(trace0) == old ? some(tid) : lock_owner(trace0);
  }
}

fixpoint bool is_lock(trace trace) {
  switch(trace) {
    case zero: return true;
    case inc(tid, trace0): return false;
    case dec(tid, trace0): return switch(lock_owner(trace0)) { case none: return false; case some(owningtid): return owningtid == tid; } && is_lock(trace0);
    case cas_(tid, old, new, trace0): return old == 0 && new == 1 && is_lock(trace0);
  }
}
@*/

/*@
lemma void execute_trace_positive_when_owned(trace t)
  requires is_lock(t) == true &*& lock_owner(t) != none;
  ensures execute_trace(t) > 0;
{
  switch(t) {
    case zero:
    case inc(tid, t0):
    case dec(tid, t0):
    case cas_(tid, old, new, t0):
      is_lock(t);
      if (execute_trace(t0) == old) {
      } else {
        execute_trace_positive_when_owned(t0);
      }
  }
}

lemma void lock_owner_preserved(trace pref, trace t, int ctid)
  requires is_good_prefix(pref, t, ctid) == true &*& is_lock(t) == true &*& lock_owner(pref) == some(ctid);
  ensures lock_owner(t) == some(ctid);
{
  switch(t) {
    case zero:
    case inc(tid, t0):
    case dec(tid, t0):
      if (pref != t) {
        lock_owner_preserved(pref, t0, ctid);
        is_lock(t);
        assert lock_owner(t0) == some(ctid);
        assert lock_owner(t0) == some(tid);
        assert tid == ctid;
      }
    case cas_(tid, old, new, t0):
      if (pref != t) {
        is_lock(t);
        lock_owner_preserved(pref, t0, ctid);
        execute_trace_positive_when_owned(t0);
      }
  }
}

lemma void dec_allowed_for_release(trace pretrace, int ctid, trace trace)
  requires lock_owner(pretrace) == some(ctid) &*& is_good_prefix(pretrace, trace, ctid) == true &*& is_lock(trace) == true;
  ensures is_lock(dec(ctid, trace)) == true;
{
  lock_owner_preserved(pretrace, trace, ctid);
}
@*/

void atomic_dec(int* c);
  //@ requires [?f]cell(c, ?allowed) &*& last_seen(c, currentThread, ?oldtrace) &*& is_dec_allowed(?lem, oldtrace, allowed, currentThread);
  //@ ensures [f]cell(c, allowed) &*& last_seen(c, currentThread, dec(currentThread, ?currtrace)) &*& is_good_prefix(oldtrace, currtrace, currentThread) == true;
  

// TODO: make this function pass the verification
void release(int* c)
  //@ requires [?f]cell(c, is_lock) &*& last_seen(c, currentThread, ?trace0) &*& lock_owner(trace0) == some(currentThread);
  //@ ensures [f]cell(c, is_lock) &*& last_seen(c, currentThread, ?trace1) &*& lock_owner(trace1) == none;
{
  /*@
  produce_lemma_function_pointer_chunk(dec_allowed_for_release(trace0, currentThread)) :
    dec_allowed(trace0, is_lock, currentThread)(trace) {
    call();
  }
  @*/
  atomic_dec(c);
}