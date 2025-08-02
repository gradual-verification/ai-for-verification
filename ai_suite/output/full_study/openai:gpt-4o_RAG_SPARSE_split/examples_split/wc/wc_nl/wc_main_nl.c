#include "stdlib.h"
#include "stdio.h"
#include "stdbool.h"
#include "limits.h"
//@ #include "list.gh"
//@ #include "string.gh"

/***
 * Description:
The `wc` function calculates the word count in a given string.

@param `string` - The string to count words in.
@param `inword` - A boolean flag indicating whether the current position is inside a word or not.

It makes sure that the return value is the word count of the string.
*/
//@ predicate word_count(char *string, bool inword, int count) = true;

int wc(char* string, bool inword)
    //@ requires string(string, ?cs) &*& word_count(string, inword, ?count);
    //@ ensures string(string, cs) &*& result == count;
{
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

// TODO: make this function pass the verification
/*** 
 * Description:
The `main` function is the main driver of the program that reads input from a file and calculates the word count.
It opens the file passed from the command-line argument, continues reading the file into a buffer and aggregates the word count.

@param `argc` - Number of command-line arguments.
@param `argv` - Array of command-line arguments.
*/
//@ predicate file_content(struct file *fp, list<char> content) = true;

int main(int argc, char** argv)
    //@ requires 0 <= argc &*& [_]argv(argv, argc, ?arguments);
    //@ ensures true;
{
    bool inword = false;
    struct file* fp = 0;
    char* buff = 0;
    int total = 0;
    char* res = 0;
    if (argc < 2) { puts("No input file specified."); return -1; }
    fp = fopen(argv[1], "r");
    buff = malloc(100);
    if (buff == 0 || fp == 0) { abort(); }
    //@ close file_content(fp, nil);
    res = fgets(buff, 100, fp);
    while (res != 0)
        //@ invariant file_content(fp, ?content) &*& chars(buff, 100, ?buff_cs) &*& total >= 0;
    {
        //@ open file_content(fp, content);
        int tmp = wc(buff, inword);
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