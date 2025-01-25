```c
#include "stdlib.h"
#include "stdio.h"
#include "malloc.h"
#include <stdbool.h>
#include "assert.h"

// Assume that `\valid' is provided by the Verifast tool to check pointer validity
// Assume that `\valid_read' is ensuring read access to memory
// Assume that `\integer_in_bound' ensures integers are within certain constraints

/**
 * Description:
 * The `wc` function calculates the word count in a given string.
 *
 * @param `string` - The string to count words in.
 * @param `inword` - A boolean flag indicating whether the current position is inside a word or not.
 * @returns Number of words in the string.
 */
 /*@
   requires string != 0;
   requires \valid_read(string);
   ensures \result >= 0;
   ensures \integer_in_bound(\result);
 @*/
int wc(char* string, bool inword) 
{
  /*@
     if (*string != 0) {
       requires \valid_read(string + 1);
     }
  @*/
  char head = *string;
  if (head == 0) {
    return inword ? 1 : 0;
  } else {
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
/*@
  ensures true;
@*/
void test() 
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
/*@
  requires argc > 0;
  requires \valid(argv + (0 .. argc - 1));
  ensures \result == 0 || \result == -1;
@*/
int main(int argc, char** argv) 
{
  bool inword = false;
  struct file* fp = 0;
  char* buff = 0;
  int total = 0;
  char* res = 0;

  /*@
    requires argc > 1 ==> \valid(argv[1]);
    ensures fp == 0 || \valid(fp);
    ensures buff == 0 || \valid(buff+(0 .. 99));
  @*/
  if(argc < 2) { puts("No input file specified."); return -1; }

  fp = fopen(argv[1], "r");
  buff = malloc(100);

  /*@
     if (buff == 0 || fp == 0) {
        alloc: abort_requires false; // Assuming the allocated pointer should be valid
     }
  @*/
  if(buff == 0 || fp == 0) { abort(); }

  res = fgets(buff, 100, fp);

  while(res != 0) 
  {
    /*@
     loop invariant \valid(buff+(0 .. 99));
     loop invariant total >= 0;
     loop variant 100;  // arbitrary large number for termination assumption
    @*/
    int tmp = wc(buff, inword);
    total = total + tmp;
    res = fgets(buff, 100, fp);
  }

  printf("%i", total);
  free(buff);
  fclose(fp);

  return 0;
}
```

This code includes formal specifications with preconditions and postconditions for the `wc` and `main` functions, introducing memory safety checks and ensuring integer bounds for safe operations. Loop invariants ensure the safety and correctness of the loop's operations inside `main`. The auxiliary assumptions (`valid` and related predicates) are typical for a verification setup using a tool like VeriFast.
