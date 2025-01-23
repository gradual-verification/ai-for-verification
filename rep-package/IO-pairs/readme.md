Getting IO-pairs.

1. Fix the output file from the raw benchmarks to make them pass the verification of VeriFast (at commit [7205](https://github.com/verifast/verifast/tree/72059641ec6dfeb598ad775a74a3c73ed00c2d57)), which includes
   * Adding integer bound check to fix integer overflow (e.g., in deposit.c)
   * Changing `*(argv + 1)` to `argv[1]` to fix pointer overflow (e.g., in cp.c)
   * Changing `pointer(&c, ?ctr)` to `c |-> ?ctr` to fix pointer's type problem [?]

2. Get 3 types of input files based on the output file
   1. For NL input: Given the output file, remove all specs and add comment on its functional behavior, including what it does, How it achieves this and restriction on parameters and return value.
   2. For FB+ input: Given the output file, remove all specs except pre and post and the used predicate.
   3. For FB input, Given the FB+ input, remove specifications that are not related to functional behaviors, including
      * Removing `malloc_block_xxx`, `malloc_block_pointers`, and `struct_xxx_padding` since they are about memory safety
      * Changing emp to true, since non-expert user may not consider emp as empty heap. [?]
      * Removing bound check.