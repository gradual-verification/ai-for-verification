```c
#include "stdlib.h"
#include "stdio.h"
#include "string.h"
#include "stdbool.h"
#include "limits.h"
#include "math.h"

/*@
inductive chars = nil | cons(char, chars);

fixpoint int length(chars cs) {
    switch(cs) {
        case nil: return 0;
        case cons(h, t): return 1 + length(t);
    }
}

fixpoint int wcount(chars cs, bool inword) {
    switch(cs) {
        case nil: return inword ? 1 : 0;
        case cons(h, t): return h == 0 ? 
            (inword ? 1 : 0) : 
            (h == ' ' ? ((inword ? 1 : 0) + wcount(t, false)) : wcount(t, true));
    }
}

predicate c_string(char *s; chars cs) =
    cs == nil ? s[0] == 0 : 
    s[0..1] |-> ?c &*& 
    c != 0 &*& 
    c_string(s + 1, ?tcs) &*&
    cs == cons(c, tcs);

predicate c_string_nt(char *s; chars cs) = 
    c_string(s, ?cs0) &*& cs == cs0 &*& nth(length(cs) - 1, cs) == 0;

predicate malloc_block(char *p; int size);

@*/

int wc(char* string, bool inword)
    //@ requires [?f]c_string_nt(string, ?cs);
    //@ ensures [f]c_string_nt(string, cs) &*& result == wcount(cs, inword);
{
    //@ open [f]c_string_nt(string, cs);
    //@ open [f]c_string(string, cs);
    char head = *string;
    if(head == 0)
    {
        //@ close [f]c_string(string, cs);
        //@ close [f]c_string_nt(string, cs);
        return inword ? 1 : 0;
    }
    else
    {
        //@ assert cs == cons(head, ?tcs);
        int result;
        if(head == ' ')
        {
            result = wc(string + 1, false);
            return inword ? 1 + result : result;
        }
        else
        {
            result = wc(string + 1, true);
            return result;
        }
        //@ close [f]c_string(string, cs);
        //@ close [f]c_string_nt(string, cs);
    }
}

void test()
    //@ requires true;
    //@ ensures true;
{
    char* test_string = "This line of text contains 8 words.";
    //@ chars test_cs = cons('T', cons('h', cons('i', cons('s', cons(' ', cons('l', cons('i', cons('n', cons('e', cons(' ', cons('o', cons('f', cons(' ', cons('t', cons('e', cons('x', cons('t', cons(' ', cons('c', cons('o', cons('n', cons('t', cons('a', cons('i', cons('n', cons('s', cons(' ', cons('8', cons(' ', cons('w', cons('o', cons('r', cons('d', cons('s', cons('.', cons(0, nil))))))))))))))))))))))))))))))))));
    int nb = wc(test_string, false);
    assert(nb == 7);
}

int main(int argc, char** argv)
    //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
    //@ ensures true;
{
    bool inword = false;
    FILE* fp;
    char* buff;
    int total = 0;
    if(argc < 2)
    {
        puts("No input file specified.");
        return -1;
    }
    fp = fopen(argv[1], "r");
    if(fp == 0)
    {
        abort();
    }
    buff = malloc(100);
    //@ assume(buff != 0);
    //@ malloc_block(buff, 100);
    if(buff == 0)
    {
        fclose(fp);
        abort();
    }
    char* res = fgets(buff, 100, fp);
    while(res != 0)
    {
        //@ c_string_nt(buff, ?cs);
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
