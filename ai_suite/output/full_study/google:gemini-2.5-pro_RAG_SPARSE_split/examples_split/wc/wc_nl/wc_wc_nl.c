#include "stdlib.h"
#include "stdio.h"

/*@
fixpoint int word_count_spec(list<char> cs, bool inword) {
    switch (cs) {
        case nil:
            return inword ? 1 : 0;
        case cons(h, t):
            if (h == ' ') {
                int result = word_count_spec(t, false);
                return inword ? 1 + result : result;
            } else {
                int result = word_count_spec(t, true);
                return result;
            }
    }
}
@*/

// TODO: make this function pass the verification
/***
 * Description:
The `wc` function calculates the word count in a given string.

@param `string` - The string to count words in.
@param `inword` - A boolean flag indicating whether the current position is inside a word or not.

It makes sure that the return value is the word count of the string.
*/
int wc(char* string, bool inword)
    //@ requires string(string, ?cs);
    //@ ensures string(string, cs) &*& result == word_count_spec(cs, inword);
{
  //@ open string(string, cs);
  char head = *string;
  if(head == 0) {
    //@ close string(string, cs);
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      //@ close string(string, cs);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      //@ close string(string, cs);
      return result;
    }
  }
}