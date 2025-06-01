#include "stdio.h"
#include "stdlib.h"

/***
 * Description:
 * The `main` function reads the contents of a file specified as a command-line argument
 * and prints each line to the standard output.
 *
 * @param argc - The number of command-line arguments.
 * @param argv - An array of strings containing the command-line arguments.
 *
 */
int main(int argc, char** argv) //@ : main
{
  struct file* fp = 0; char* buffer = 0; char* res = 0;
  if(argc < 2) { fputs("Enter a file name.", stderr); return -1; }
  fp = fopen(argv[1], "r");
  buffer = malloc(sizeof(char) * 100);
  res = 0;
  if(fp == 0 || buffer == 0) { abort(); }
  res = fgets(buffer, 100, fp);
  while(res != 0) d
  {
    puts(buffer);
    res = fgets(buffer, 100, fp);
  }
  free((void *)buffer);
  fclose(fp);
  return 0;
}
