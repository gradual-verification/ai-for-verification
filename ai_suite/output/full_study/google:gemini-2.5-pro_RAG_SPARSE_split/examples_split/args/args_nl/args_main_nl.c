#include "stdio.h"

/*@
// A predicate to hold the memory chunks of the processed part of the argv array.
// It is defined recursively.
// - `argv`: The start of the original array.
// - `i`: The number of arguments processed so far.
// - `processed_arguments`: A list of the character lists of the processed strings.
predicate processed_argv(char **argv, int i, list<list<char> > processed_arguments) =
    i == 0 ?
        // Base case: no arguments processed yet.
        processed_arguments == nil
    :
        // Recursive step: holds the chunks for the (i-1)-th argument,
        // plus the predicate for the first i-1 arguments.
        processed_argv(argv, i - 1, ?prefix) &*&
        [_]*(argv + i - 1) |-> ?p &*& [_]string(p, ?cs) &*&
        processed_arguments == append(prefix, cons(cs, nil));
@*/

// TODO: make this function pass the verification
/***
 * Description:
 * The `main` function prints each command-line argument to the standard output.
 *
 * @param argc - the number of command-line arguments.
 * @param argv - an array of strings containing the command-line arguments.
 * 
 */
int main(int argc, char **argv)
    //@ : main
{
    // Initially, no arguments have been processed.
    //@ close processed_argv(argv, 0, nil);
    for (int i = 0; i < argc; i++)
        /*@
        invariant 0 <= i &*& i <= argc &*&
                    // The first `i` arguments are held by `processed_argv`.
                    processed_argv(argv, i, take(i, arguments)) &*&
                    // The remaining arguments are still in the `argv` predicate.
                    [_]argv(argv + i, argc - i, drop(i, arguments));
        @*/
    {
        // Open the `argv` predicate to get access to the i-th argument.
        //@ open argv(argv + i, argc - i, drop(i, arguments));
        
        // `puts` requires a `string` predicate, which we now have.
        puts(*(argv + i));
        
        // The i-th argument is now processed. We add its chunks to our
        // `processed_argv` predicate to maintain the invariant for the next iteration.
        //@ close processed_argv(argv, i + 1, take(i + 1, arguments));
    }
    
    // After the loop, `i == argc`. The invariant holds, so we have:
    // `processed_argv(argv, argc, arguments)` and `[_]argv(argv + argc, 0, nil)`.
    // The `ensures junk()` from the `main` contract will consume these chunks.
    return 0;
}