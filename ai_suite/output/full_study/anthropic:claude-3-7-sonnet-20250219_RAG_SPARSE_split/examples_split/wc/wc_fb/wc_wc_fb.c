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
//@ requires [?f]string(string, ?cs);
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  char head = * string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      //@ open string(string, cs);
      //@ assert cs == cons(head, ?tail);
      //@ close string(string + 1, tail);
      int result = wc(string + 1, false);
      //@ open string(string + 1, tail);
      //@ close string(string, cs);
      return inword ? 1 + result: result;
    } else {
      //@ open string(string, cs);
      //@ assert cs == cons(head, ?tail);
      //@ close string(string + 1, tail);
      int result = wc(string + 1, true);
      //@ open string(string + 1, tail);
      //@ close string(string, cs);
      return result;
    }
  }
}