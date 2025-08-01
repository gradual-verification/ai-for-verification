#include "stdlib.h"
#include "stdbool.h"

struct bst_node {
 struct bst_node *left;
 struct bst_node *right;
 int value;
};

/*@ 
predicate bst(struct bst_node *node, int min, int max) =
 node ==0 ?
 true
 :
 malloc_block_bst_node(node) &*&
 node->value |-> ?v &*& min < v &*& v < max &*&
 node->left |-> ?left &*& node->right |-> ?right &*&
 bst(left, min, v) &*& bst(right, v, max);
@*/

// TODO: make this function pass the verification
struct bst_node *bst_create()
/*@
  requires true;
  ensures bst(result, INT_MIN, INT_MAX);
@*/
{
  struct bst_node *node = malloc(sizeof(struct bst_node));
  if(node == 0) abort();
  node->value = 0;
  node->left = 0;
  node->right = 0;
  return node;
}