#include "stdlib.h"
#include "stdio.h"

struct file;
//@ predicate file(struct file* f);

struct file* fopen(char* filename, char* mode);
//@ requires [?f1]string(filename, ?s1) &*& [?f2]string(mode, ?s2);
//@ ensures result == 0 ? true : file(result);

void fclose(struct file* f);
//@ requires file(f);
//@ ensures true;

size_t fread(void* ptr, size_t size, size_t nmemb, struct file* stream);
//@ requires chars(ptr, size * nmemb, _) &*& file(stream);
//@ ensures chars(ptr, size * nmemb, _) &*& file(stream);

size_t fwrite(const void* ptr, size_t size, size_t nmemb, struct file* stream);
//@ requires [?f]chars(ptr, size * nmemb, _) &*& file(stream);
//@ ensures [f]chars(ptr, size * nmemb, _) &*& file(stream);

int puts(const char *s);
//@ requires [?f]string(s, ?cs);
//@ ensures true;

void* malloc(size_t size);
//@ requires 0 <= size;
//@ ensures result == 0 ? true : malloc_block(result, size);

void free(void* ptr);
//@ requires malloc_block(ptr, _);
//@ ensures true;

int main(int argc, char** argv) //@ : main
//@ requires 0 <= argc &*& argv(argv, argc, _);
//@ ensures true;
{
    struct file* from = 0; struct file* to = 0; char* buffer = 0;
    size_t nb_read = 0;
    if(argc < 3) { puts("Not enough parameters."); return -1; }
    //@ open argv(argv, argc, _);
    //@ assume(argv[1] != 0 && argv[2] != 0);
    //@ close [1/2]string(argv[1], _);
    //@ close [1/2]string("r", _);
    from = fopen(argv[1], "r");
    //@ open [1/2]string("r", _);
    //@ close [1/2]string(argv[2], _);
    //@ close [1/2]string("w", _);
    to = fopen(argv[2], "w");
    //@ open [1/2]string("w", _);
    buffer = malloc(100);
    if(buffer == 0 || from == 0 || to == 0) { abort(); }
    //@ malloc_block(buffer, 100);
    //@ chars(buffer, 100, _);
    nb_read = fread(buffer, 1, 100, from);
    while(0 < nb_read)
    //@ invariant chars(buffer, 100, _) &*& file(from) &*& file(to);
    {
        size_t nb_written = fwrite(buffer, 1, nb_read, to);
        nb_read = fread(buffer, 1, 100, from);
    }
    //@ open chars(buffer, 100, _);
    fclose(from);
    fclose(to);
    free(buffer);
    return 0;
}
