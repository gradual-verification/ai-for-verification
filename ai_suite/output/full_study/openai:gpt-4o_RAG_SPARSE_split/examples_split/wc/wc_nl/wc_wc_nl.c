#include "stdlib.h"
#include "stdio.h"
#include "stdbool.h"
#include "string.h"

//@ #include "list.gh"
//@ #include "nat.gh"

/*@
predicate word_count(char *string, int count) =
    string == 0 ?
        count == 0
    :
        string[0..strlen(string)] |-> ?cs &*&
        count == length(filter((char c) { return c != ' '; }, cs)) - length(filter((char c) { return c == ' '; }, cs)) + 1;
@*/

/*@
fixpoint int count_words(list<char> cs, bool inword) {
    switch (cs) {
        case nil: return inword ? 1 : 0;
        case cons(h, t): return
            h == ' ' ?
                (inword ? 1 : 0) + count_words(t, false)
            :
                count_words(t, true);
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
/*@
requires string(string, ?cs) &*& inword == false;
ensures string(string, cs) &*& result == count_words(cs, inword);
@*/
int wc(char* string, bool inword)
{
  char head = *string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      return inword ? 1 + result: result;
    } else {
      int result = wc(string + 1, true);
      return result;
    }
  }
}