#include "stdlib.h"
#include "stdio.h"

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}
@*/

// TODO: make this function pass the verification
int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs);
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  char head = *string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ assert [f]string(string + 1, ?cs1);
      //@ assert cs == cons(head, cs1);
      //@ assert wcount(cs, inword) == (inword ? 1 + wcount(cs1, false) : wcount(cs1, false));
      return inword ? 1 + result : result;
    } else {
      int result = wc(string + 1, true);
      //@ assert [f]string(string + 1, ?cs1);
      //@ assert cs == cons(head, cs1);
      //@ assert wcount(cs, inword) == wcount(cs1, true);
      return result;
    }
  }
}