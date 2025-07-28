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


int atomic_cas(int* c, int old, int new);
  //@ requires [?f]cell(c, ?allowed) &*& last_seen(c, currentThread, ?oldtrace) &*& is_cas_allowed(?lem, oldtrace, allowed, old, new);
  //@ ensures [f]cell(c, allowed) &*& last_seen(c, currentThread, cas_(currentThread, old, new, ?currtrace)) &*& is_good_prefix(currtrace, currtrace, currentThread) == true &*& result == execute_trace(currtrace);

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


// TODO: make this function pass the verification
void acquire(int* c)
  //@ requires [?f]cell(c, is_lock) &*& last_seen(c, currentThread, _);
  //@ ensures [f]cell(c, is_lock) &*& last_seen(c, currentThread, ?trace1) &*& lock_owner(trace1) == some(currentThread);
{
  while(true)
  {
    int read = atomic_cas(c, 0, 1);
    if(read == 0) {
      break;
    }
  }
}


