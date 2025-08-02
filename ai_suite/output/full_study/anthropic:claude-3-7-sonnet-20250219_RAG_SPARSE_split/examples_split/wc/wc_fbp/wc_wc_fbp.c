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

int wc(char* string, bool inword)
//@ requires [?f]string(string, ?cs) &*& wcount(cs, inword) < INT_MAX;
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  char head = *string;
  //@ open [f]string(string, cs);
  if(head == 0) {
    //@ close [f]string(string, nil);
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      //@ assert cs == cons(head, ?tail);
      //@ close [f]string(string, cs);
      int result = wc(string + 1, false);
      //@ assert result == wcount(tail, false);
      return inword ? 1 + result : result;
    } else {
      //@ assert cs == cons(head, ?tail);
      //@ close [f]string(string, cs);
      int result = wc(string + 1, true);
      //@ assert result == wcount(tail, true);
      return result;
    }
  }
}