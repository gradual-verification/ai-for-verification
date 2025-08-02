#include "stdlib.h"
#include "stdio.h"

/*@
  // Lemma to help with the recursive verification
  lemma void wc_lemma(char* string, bool inword, int result)
    requires string[0] == 0 ? true : true;
    ensures wc(string, inword) == result;
  {
    if (*string == 0) {
      // Base case
    } else {
      if (*string == ' ') {
        // Space case
        wc_lemma(string + 1, false, inword ? 1 + result : result);
      } else {
        // Non-space case
        wc_lemma(string + 1, true, result);
      }
    }
  }
@*/

/**
 * Description:
The `wc` function calculates the word count in a given string.

@param `string` - The string to count words in.
@param `inword` - A boolean flag indicating whether the current position is inside a word or not.

It makes sure that the return value is the word count of the string.
*/
int wc(char* string, bool inword)
  /*@
    requires [?f]string(string, ?cs);
    ensures [f]string(string, cs) &*& 
            result == (inword ? 1 : 0) + 
                      (length(cs) == 0 ? 0 : 
                        (*string == ' ' ? 
                          wc(string + 1, false) : 
                          wc(string + 1, true)));
  @*/
{
  char head = *string;
  if(head == 0) {
    return inword ? 1 : 0;
  } else {
    if(head == ' ') {
      int result = wc(string + 1, false);
      return inword ? 1 + result : result;
    } else {
      int result = wc(string + 1, true);
      return result;
    }
  }
}