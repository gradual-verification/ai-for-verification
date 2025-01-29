This document shows how we get IO-pairs from VeriFast Benchmarks (see readme in `../raw_benchmark`).

1. Fix the output file from the raw benchmarks to make them pass the verification of VeriFast (at commit [7205](https://github.com/verifast/verifast/tree/72059641ec6dfeb598ad775a74a3c73ed00c2d57)), which includes
   * Fixing integer overflow (e.g., adding integer bound check in deposit.c)
   * Fixing pointer overflow (e.g., changing `*(argv + 1)` to `argv[1]` in cp.c)
   * Fixing pointer's type problem (e.g., changing `pointer(&c, ?ctr)` to `c |-> ?ctr` in globals.c)

2. Get 3 types of input files based on the output file
   1. For NL input: Given the output file, remove all specifications and add comment on its functional behavior, including what it does, How it achieves this and restriction on parameters and return value.
   2. For FB+ input: Given the output file, remove all specifications except precondition, postcondition and the used predicate.
   3. For FB input: Given the FB+ input, remove specifications that are not related to functional behaviors, including
      * Removing `malloc_block_xxx`, `malloc_block_pointers`, and `struct_xxx_padding` since they are about memory safety.
      * Changing emp to true, since emp means empty heap, not functional behavior.
      * Removing bound check.
   
   
   
   For example, in function `increment` of counter_with_pred.c, 
   
   * The output file captures functional behavior and passes the verification:
   
     ```C
     struct Counter {
       int value;
     };
     
     /*@
     predicate Counter(struct Counter* c, int v) =
       c->value |-> v &*& malloc_block_Counter(c);
     @*/
     
     void increment(struct Counter* c)
       //@ requires Counter(c, ?v) &*& v < INT_MAX;
       //@ ensures Counter(c, v+1);
     {
       //@ open Counter(c, v);
       int tmp = c->value;
       c->value = tmp + 1;
       //@ close Counter(c, v+1);
     }
     ```
   
   * The NL input file only keeps the source code and has an extra comment about functional behavior.
   
     ```c
     struct Counter {
       int value;
     };
     
     /***
      * Description:
     The increment function increments the value of the Counter structure by one.
     
     @param c - a pointer to the Counter structure to be incremented.
     @requires - the Counter structure pointed to by c must be initialized.
     @ensures - the value of the Counter structure pointed to by c is incremented by one.
     */
     void increment(struct Counter* c)
     {
       int tmp = c->value;
       c->value = tmp + 1;
     }
     ```
   
   * The FB+ input file removes all the specs except precondition, postcondition and predicate definitions.
   
     ```c
     struct Counter {
       int value;
     };
     
     /*@
     predicate Counter(struct Counter* c, int v) =
       c->value |-> v &*& malloc_block_Counter(c);
     @*/
     
     void increment(struct Counter* c)
     //@ requires Counter(c, ?v) &*& v < INT_MAX;
     //@ ensures Counter(c, v+1);
     {
       int tmp = c->value;
       c->value = tmp + 1;
     }
     ```
   
   * The FB input file only keeps the precondition, postcondition and predicate definition about functional behaviors (e.g., `malloc_block_Counter(c)` is removed since it only shows the allocated status of `c`, but not functional behavior).
   
     ```c
     struct Counter {
       int value;
     };
     
     /*@
     predicate Counter(struct Counter* c, int v) =
       c->value |-> v;
     @*/
     
     void increment(struct Counter* c)
     //@ requires Counter(c, ?v);
     //@ ensures Counter(c, v+1);
     {
       int tmp = c->value;
       c->value = tmp + 1;
     }
     ```
   
     