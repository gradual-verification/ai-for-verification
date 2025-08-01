#include "stdlib.h"
#include "stdio.h"


// TODO: make this function pass the verification
/***
 * Description:
The `wc` function calculates the word count in a given string.

@param `string` - The string to count words in.
@param `inword` - A boolean flag indicating whether the current position is inside a word or not.

It makes sure that the return value is the word count of the string.
*/
int wc(char* string, bool inword)
{
  char head = * string;
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


