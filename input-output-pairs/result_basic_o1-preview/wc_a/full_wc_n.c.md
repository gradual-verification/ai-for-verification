```c
#include "stdlib.h"
#include "stdio.h"
#include "string.h"
#include "stdbool.h"

/*@
fixpoint int word_count(list<char> cs, bool inword) {
    switch(cs) {
        case nil: 
            return inword ? 1 : 0;
        case cons(c, cs0):
            if (c == ' ') {
                return (inword ? 1 : 0) + word_count(cs0, false);
            } else {
                return word_count(cs0, true);
            }
    }
}

predicate string(char* p; list<char> cs) = 
    cs == nil ? p[0] |-> '\0' :
    p[0] |-> ?c &*& c != '\0' &*& string(p + 1, ?cs0) &*& cs == cons(c, cs0);
@*/

/*@
requires [?f]string(string, ?cs);
ensures [f]string(string, cs) &*& result == word_count(cs, inword);
decreases length(cs);
@*/
int wc(char* string, bool inword)
{
    //@ open [f]string(string, cs);
    char head = *string;
    if (head == '\0') {
        //@ close [f]string(string, cs);
        return inword ? 1 : 0;
    } else {
        //@ assert cs == cons(head, ?cs0);
        if (head == ' ') {
            //@ close [f]string(string, cs);
            int result = wc(string + 1, false);
            return inword ? 1 + result : result;
        } else {
            //@ close [f]string(string, cs);
            int result = wc(string + 1, true);
            return result;
        }
    }
}

/*@
requires true;
ensures true;
@*/
void test()
{
    char* s = "This line of text contains 8 words.";
    //@ list<char> cs = {'T','h','i','s',' ','l','i','n','e',' ','o','f',' ','t','e','x','t',' ','c','o','n','t','a','i','n','s',' ','8',' ','w','o','r','d','s','.', '\0'};
    //@ close string(s, butlast(cs));
    int nb = wc(s, false);
    //@ open string(s, butlast(cs));
    //@ assert nb == word_count(butlast(cs), false);
    //@ assert nb == 7;
    assert(nb == 7);
    //@ leak string(s, butlast(cs));
}

/*@
requires true;
ensures true;
@*/
int main()
{
    test();
    return 0;
}
```
