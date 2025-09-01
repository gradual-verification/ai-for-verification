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



int atomic_load(int* c);
  //@ requires [?f]cell(c, ?allowed) &*& last_seen(c, currentThread, ?oldtrace);
  //@ ensures [f]cell(c, allowed) &*& last_seen(c, currentThread, ?currtrace) &*& is_good_prefix(oldtrace, currtrace, currentThread) == true &*& execute_trace(currtrace) == result;
  
  

// TODO: make this function pass the verification
void only_allow_incrementing(int* c)
  //@ requires [?f]cell(c, incr_only) &*& last_seen(c, currentThread, ?trace0);
  //@ ensures [f]cell(c, incr_only) &*& last_seen(c, currentThread, _);
{
  int x1 = atomic_load(c);
  int x2 = atomic_load(c);
  assert(x1 <= x2);
}


