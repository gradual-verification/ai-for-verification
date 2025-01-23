#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

// Assume that `\valid' is provided by the Verifast tool to check pointer validity
// Assume that `\valid_read' is ensuring read access to memory
// Assume that `\integer_in_bound' ensures integers are within certain constraints

/*@
fixpoint int wcount(list<char> cs, bool inword) {
  switch(cs) {
    case nil: return inword ? 1 : 0;
    case cons(h, t): return 0 == h ? (inword ? 1 : 0) : (' ' == h ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
  }
}

lemma void wcount_in_range(list<char> cs, bool inword)
  requires true;
  ensures wcount(cs, inword) >= 0 &*& wcount(cs, inword) <= length(cs) + 1;
{
  switch(cs) {
    case nil:
      // Base case: if the list is empty, wcount(cs, inword) is either 0 or 1,
      // and length(cs) is 0, so the result is valid.
      if (inword) {
        assert wcount(cs, inword) == 1;
      } else {
        assert wcount(cs, inword) == 0;
      }
      assert wcount(cs, inword) <= length(cs) + 1;
      break;
    case cons(h, t):
      // Recursive case: process the head and the tail of the list.
      wcount_in_range(t, false); // Call lemma for tail with false
      wcount_in_range(t, true);  // Call lemma for tail with true
      if (h == 0) {
        // If head is the null character, wcount(cs, inword) is either 0 or 1,
        // which is still less than or equal to length(cs).
        assert wcount(cs, inword) == (inword ? 1 : 0);
      } else if (h == ' ') {
        // If the head is a space, the wcount either increments or remains the same.
        // The word count is still less than or equal to the total length.
        assert wcount(cs, inword) == (inword ? 1 + wcount(t, false) : wcount(t, false));
      } else {
        // If the head is a non-space character, we proceed with the count from the tail.
        assert wcount(cs, inword) == wcount(t, true);
      }
      // Finally, assert that wcount(cs, inword) is less than or equal to length(cs).
      assert wcount(cs, inword) <= length(cs) + 1;
      break;
  }
}
@*/

/**
 * Description:
 * The `wc` function calculates the word count in a given string.
 *
 * @param `string` - The string to count words in.
 * @param `inword` - A boolean flag indicating whether the current position is inside a word or not.
 * @returns Number of words in the string.
 */
 /* @
   requires string != 0;
   requires \valid_read(string);
   ensures \result >= 0;
   ensures \integer_in_bound(\result);
 @ */
int wc(char* string, bool inword) 
//@ requires [?f]string(string, ?cs) &*& wcount(cs, inword) < INT_MAX;
//@ ensures [f]string(string, cs) &*& result == wcount(cs, inword);
{
  /* @
     if (*string != 0) {
       requires \valid_read(string + 1);
     }
  @ */
  char head = *string;
  if (head == 0) {
    return inword ? 1 : 0;
  } else {
    //@ string_limits(string);
    if (head == ' ') {
      int result = wc(string + 1, false);
      return inword ? 1 + result : result;
    } else {
      int result = wc(string + 1, true);
      return result;
    }
  }
}

/**
 * Description:
 * The `test` function is a test function to validate the `wc` function.
 */

void test() 
//@ requires true;
//@ ensures true;
{
  int nb = wc("This line of text contains 8 words.", false);
  assert(nb == 7);
}

/**
 * Description:
 * The `main` function is the main driver of the program that reads input from a file and calculates the word count.
 * It opens the file passed from the command-line argument, continues reading the file into a buffer and aggregates the word count.
 *
 * @param `argc` - Number of command-line arguments.
 * @param `argv` - Array of command-line arguments.
 * @returns Exit code indicating success or failure.
 */
/* @
  requires argc > 0;
  requires \valid(argv + (0 .. argc - 1));
  ensures \result == 0 || \result == -1;
@ */
int main(int argc, char** argv) 
//@ requires 0 <= argc &*& [_]argv(argv, argc, _);
//@ ensures true;
{
  bool inword = false;
  struct file* fp = 0;
  char* buff = 0;
  int total = 0;
  char* res = 0;

  /* @
    requires argc > 1 ==> \valid(argv[1]);
    ensures fp == 0 || \valid(fp);
    ensures buff == 0 || \valid(buff+(0 .. 99));
  @ */
  if(argc < 2) { puts("No input file specified."); return -1; }
  //@ open [_]argv(argv, argc, _);
  //@ open [_]argv(argv + 1, argc - 1, _);
  fp = fopen(argv[1], "r");
  buff = malloc(100);

  /* @
     if (buff == 0 || fp == 0) {
        alloc: abort_requires false; // Assuming the allocated pointer should be valid
     }
  @ */
  if(buff == 0 || fp == 0) { abort(); }

  res = fgets(buff, 100, fp);

  while(res != 0) 
  //@ invariant file(fp) &*& (res != 0 ? string(buff, ?scs) &*& buff[length(scs) + 1..100] |-> _ : buff[..100] |-> _) &*& total >= 0;
  {
    /* @
     loop invariant \valid(buff+(0 .. 99));
     loop invariant total >= 0;
     loop variant 100;  // arbitrary large number for termination assumption
    @ */
    //@ assert string(buff, ?scs);
    //@ wcount_in_range(scs, inword);
    int tmp = wc(buff, inword);
    //@ string_to_chars(buff);
    if (total > INT_MAX - tmp) {
      break;
    }
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }

  printf("%i", total);
  free(buff);
  fclose(fp);

  return 0;
}
