#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "string.h"
#include "chars.gh"
#include "assert.h"

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return h == 0 ? (inword ? 1 : 0) : (h == ' ' ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}

lemma void wcount_cons(char c, list<char> cs0, bool inword)
  requires true;
  ensures wcount(cons(c, cs0), inword) == (c == 0 ? (inword ? 1 : 0) : (c == ' ' ? (inword ? 1 : 0) + wcount(cs0, false) : wcount(cs0, true)));
{
  // Proof by unfolding the fixpoint
}

@*/

int wc(char* string, bool inword)
    //@ requires [?f]string(string, ?cs);
    //@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
    //@ open [f]string(string, cs);
    char c = *string;
    if(c == 0) {
        //@ assert cs == cons(0, nil);
        //@ wcount_cons(c, nil, inword);
        //@ close [f]string(string, cs);
        return inword ? 1 : 0;
    } else {
        //@ cs == cons(c, ?cs0);
        //@ close [f]string(string + 1, cs0);

        if(c == ' ') {
            int result = wc(string + 1, false);
            //@ wcount_cons(c, cs0, inword);
            //@ assert wcount(cs, inword) == (inword ? 1 : 0) + wcount(cs0, false);
            //@ close [f]string(string, cs);
            return inword ? 1 + result : result;
        } else {
            int result = wc(string + 1, true);
            //@ wcount_cons(c, cs0, inword);
            //@ assert wcount(cs, inword) == wcount(cs0, true);
            //@ close [f]string(string, cs);
            return result;
        }
    }
}

void test() 
//@ requires true;
//@ ensures true;
{
    int nb = wc("This line of text contains 8 words.", false);
    //@ assert(nb == 7);
    //@ assert true; // Ensure verification continues
}

int main()
//@ requires true;
//@ ensures true;
{
    test();
    return 0;
}
