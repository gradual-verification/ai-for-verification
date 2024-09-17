#include "stdio.h"
#include "malloc.h"
#include "stdlib.h"

/* Description
  Behavior: The main function is the entry point of the program. It checks if a file name is provided as a command-line argument, reads the contents of the file, and prints them to the standard output (stdout).
    - Parameters: 
      - `argc`: Number of command-line arguments passed to the program.
      - `argv`: Array of command-line arguments provided to the program.
*/
int main(int argc, char** argv)
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  if(argc < 2) { puts("Enter a file name."); return -1; }
  fp = fopen(* (argv + 1), "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  if(fp == 0 || buffer == 0) { abort(); }
  res = fgets(buffer, 100, fp);
  while(res != 0) 
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  free(buffer);
  fclose(fp);
  return 0;
}