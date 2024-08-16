
#include "malloc.h"
#include "stdlib.h"
#include <stdbool.h>

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@

inductive tree =
    empty
  | tree(struct node *, tree, tree);

fixpoint int tcount(tree nodes) {
  switch (nodes) {
    case empty: return 0;
    case tree(root, left, right):
      return 1 + tcount(left) + tcount(right);
  }
}

lemma void tcount_nonnegative(tree nodes)
  requires true;
  ensures 0 <= tcount(nodes);
{
  switch (nodes) {
    case empty:
    case tree(n, l, r):
      tcount_nonnegative(l);
      tcount_nonnegative(r);
  }
}

predicate subtree(struct node * root, struct node * parent, tree t) =
  switch (t) {
    case empty: return root == 0;
    case tree(root0, leftNodes, rightNodes):
      return
        root == root0 &*& root != 0 &*&
        root->left |-> ?left &*&
        root->right |-> ?right &*&
        root->parent |-> parent &*&
        root->count |-> tcount(t) &*&
        malloc_block_node(root) &*&
        subtree(left, root, leftNodes) &*&
        subtree(right, root, rightNodes);
  };

inductive context =
    root
  | left_context(context, struct node *, tree)
  | right_context(context, struct node *, tree);

predicate context(struct node * node, struct node * parent,
                  int count, context nodes) =
  switch (nodes) {
    case root: return parent == 0;
    case left_context(pns, parent0, rightNodes):
      return
        parent == parent0 &*& parent != 0 &*&
        parent->left |-> node &*&
        parent->right |-> ?right &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        malloc_block_node(parent) &*&
        context(parent, gp, pcount, pns) &*&
        subtree(right, parent, rightNodes) &*&
        pcount == 1 + count + tcount(rightNodes);
    case right_context(pns, parent0, leftNodes):
      return
        parent == parent0 &*& parent != 0 &*&
        parent->left |-> ?left &*&
        parent->right |-> node &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        malloc_block_node(parent) &*&
        context(parent, gp, pcount, pns) &*&
        subtree(left, parent, leftNodes) &*&
        pcount == 1 + tcount(leftNodes) + count;
  };

predicate tree(struct node * node, context c, tree subtree) =
  context(node, ?parent, tcount(subtree), c) &*&
  subtree(node, parent, subtree);

@*/

/*
  Natural Language Specification:
  - Description: Creates a new node in the tree with the specified parent node, and initializes its left and right children as empty.
  - Parameters: `p` - a pointer to the parent node.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to the newly created node, and the subtree rooted at this node is correctly initialized.
*/
struct node *create_node(struct node *p)
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0; 
  n->right = 0; 
  n->count = 1;
  
  return n;
}

/*
  Natural Language Specification:
  - Description: Creates a new tree with a single root node.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: Returns a pointer to the root node of the newly created tree.
*/
struct node *create_tree()
{
  struct node *n = create_node(0);
 
  return n;
}

/*
  Natural Language Specification:
  - Description: Retrieves the count of nodes in the subtree rooted at the specified node.
  - Parameters: `node` - a pointer to the root of the subtree.
  - Requires: The subtree rooted at `node` is valid.
  - Ensures: Returns the count of nodes in the subtree and ensures it is non-negative.
*/
int subtree_get_count(struct node *node)
  
{
  int result = 0;
 
  if (node != 0) { result = node->count; }
 
  return result;
}

/*
  Natural Language Specification:
  - Description: Updates the count of nodes in the subtree for all ancestor nodes starting from the specified node.
  - Parameters: 
    - `n` - a pointer to the current node.
    - `p` - a pointer to the parent node.
    - `count` - the updated count of nodes in the subtree rooted at the current node.
  - Requires: The context of the node and its parent is valid, and the count is non-negative.
  - Ensures: The context is updated with the correct count, and the node's left child remains unchanged.
*/
void fixup_ancestors(struct node *n, struct node *p, int count)
{
 
  if (p == 0) {
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
     
      leftCount = count;
      rightCount = subtree_get_count(right);
    } else {
      leftCount = subtree_get_count(left);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
    }
  }
 
}

/*
  Natural Language Specification:
  - Description: Adds a new left child to the specified node in the tree.
  - Parameters: `node` - a pointer to the node to which the left child will be added.
  - Requires: 
    - The tree rooted at `node` is valid.
    - The left subtree of `node` is empty.
  - Ensures: Returns a pointer to the newly added left child, and the tree is correctly updated.
*/
struct node *tree_add_left(struct node *node)
{

  struct node *n = create_node(node);

  {
      struct node *nodeLeft = node->left;
  
      node->left = n;
  
      fixup_ancestors(n, node, 1);
     
  }
 
  return n;
}

/*
  Natural Language Specification:
  - Description: Adds a new right child to the specified node

 in the tree.
  - Parameters: `node` - a pointer to the node to which the right child will be added.
  - Requires: 
    - The tree rooted at `node` is valid.
    - The right subtree of `node` is empty.
  - Ensures: Returns a pointer to the newly added right child, and the tree is correctly updated.
*/
struct node *tree_add_right(struct node *node)
{
   
    struct node *n = create_node(node);

    {
        struct node *nodeRight = node->right;
       
        node->right = n;
       
        fixup_ancestors(n, node, 1);

    }

    return n;
}

/*
  Natural Language Specification:
  - Description: Retrieves the parent node of the specified node in the tree.
  - Parameters: `node` - a pointer to the current node.
  - Requires: 
    - The tree rooted at `node` is valid.
    - `node` is not the root of the tree.
  - Ensures: Returns the parent node of `node`, and the tree is correctly updated.
*/
struct node *tree_get_parent(struct node *node)
{
  
  struct node *p = node->parent;
  
  return p;
}

/*
  Natural Language Specification:
  - Description: Recursively frees all memory associated with the subtree rooted at the specified node.
  - Parameters: `node` - a pointer to the root of the subtree to be disposed.
  - Requires: The subtree rooted at `node` is valid.
  - Ensures: All memory associated with the subtree is freed.
*/
void subtree_dispose(struct node *node)

{
  
  if (node != 0) {
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
  }
}

/*
  Natural Language Specification:
  - Description: Frees all memory associated with the tree rooted at the specified node.
  - Parameters: `node` - a pointer to the root of the tree to be disposed.
  - Requires: The tree rooted at `node` is valid.
  - Ensures: All memory associated with the tree is freed.
*/
void tree_dispose(struct node *node)
 
{
  
  subtree_dispose(node);
}

/*
  Natural Language Specification:
  - Description: Main function that creates a tree, adds left and right children, and then disposes of the tree.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: No specific postconditions.
*/
int main0()

{
  struct node *node = create_tree();
  node = tree_add_left(node);
  node = tree_add_right(node);
  node = tree_get_parent(node);
  node = tree_add_left(node);
  node = tree_get_parent(node);
  node = tree_get_parent(node);
  tree_dispose(node);
  return 0;
}

/*@

fixpoint tree combine(context c, tree t) {
    switch (c) {
        case root: return t;
        case left_context(pns, p, right):
          return combine(pns, tree(p, t, right));
        case right_context(pns, p, left):
          return combine(pns, tree(p, left, t));
    }
}

inductive path = here | left(path) | right(path);

fixpoint bool contains_at_path(tree nodes, path path, struct node *node) {
    switch (nodes) {
        case empty: return false;
        case tree(rootNode, leftNodes, rightNodes):
            return
                switch (path) {
                    case here: return node == rootNode;
                    case left(path0): return contains_at_path(leftNodes, path0, node);
                    case right(path0): return contains_at_path(rightNodes, path0, node);
                };
    }
}

lemma void go_to_root(context contextNodes)
    requires tree(?node, contextNodes, ?subtreeNodes);
    ensures tree(?rootNode, root, combine(contextNodes, subtreeNodes));
{
    switch (contextNodes) {
        case root:
        case left_context(parentContextNodes, parent, rightNodes):
            open tree(node, contextNodes, subtreeNodes);
            open context(node, _, _, _);
            assert context(parent, ?grandparent, _, _);
            close subtree(parent, grandparent, tree(parent, subtreeNodes, rightNodes));
            close tree(parent, parentContextNodes, tree(parent, subtreeNodes, rightNodes));
            go_to_root(parentContextNodes);
        case right_context(parentContextNodes, parent, leftNodes):
            open tree(node, contextNodes, subtreeNodes);
            open context(node, _, _, _);
            assert context(parent, ?grandparent, _, _);
            close subtree(parent, grandparent, tree(parent, leftNodes, subtreeNodes));
            close tree(parent, parentContextNodes, tree(parent, leftNodes, subtreeNodes));
            go_to_root(parentContextNodes);
    }
}

fixpoint path combine_path(context contextNodes, path path) {
    switch (contextNodes) {
        case root: return path;
        case left_context(parentContextNodes, parent, rightNodes): return combine_path(parentContextNodes, left(path));
        case right_context(parentContextNodes, parent, leftNodes): return combine_path(parentContextNodes, right(path));
    }
}

fixpoint context get_context_nodes_at_path(context contextNodes, tree subtreeNodes, path path) {
    switch (path) {
        case here: return contextNodes;
        case left(path0):
            return
                switch (subtreeNodes) {
                    case empty: return contextNodes;
                    case tree(rootNode, leftNodes, rightNodes):
                        return get_context_nodes_at_path(left_context(contextNodes, rootNode, rightNodes), leftNodes, path0);
                };
        case right(path0):
            return
                switch (subtreeNodes) {
                    case empty: return contextNodes;
                    case tree(rootNode, leftNodes, rightNodes):
                        return get_context_nodes_at_path(right_context(contextNodes, rootNode, leftNodes), rightNodes, path0);
                };
    }
}

fixpoint tree get_subtree_nodes_at_path(tree subtreeNodes, path path) {
    switch (subtreeNodes) {
        case empty: return empty;
        case tree(rootNode, leftNodes, rightNodes):
            return
                switch (path) {
                    case here: return subtreeNodes;
                    case left(path0): return get_subtree_nodes_at_path(leftNodes, path0);
                    case right(path0): return get_subtree_nodes_at_path(rightNodes, path0);
                };
    }
}

lemma void go_to_descendant(struct node *node0, path path, struct node *node)
    requires tree(node0, ?contextNodes, ?subtreeNodes) &*& contains_at_path(subtreeNodes, path, node) == true;
    ensures tree(node, get_context_nodes_at_path(contextNodes, subtreeNodes, path), get_subtree_nodes_at_path(subtree

Nodes, path));
{
    switch (path) {
        case here:
            open tree(node0, contextNodes, subtreeNodes);
            open subtree(node0, ?parent, subtreeNodes);
            switch (subtreeNodes) {
                case empty:
                case tree(node00, leftNodes, rightNodes):
                    close subtree(node0, parent, subtreeNodes);
                    close tree(node0, contextNodes, subtreeNodes);
            }
        case left(path0):
            open tree(node0, contextNodes, subtreeNodes);
            open subtree(node0, ?parent, subtreeNodes);
            switch (subtreeNodes) {
                case empty:
                case tree(node00, leftNodes, rightNodes):
                    struct node *left = node0->left;
                    close context(left, node0, tcount(leftNodes), left_context(contextNodes, node0, rightNodes));
                    close tree(left, left_context(contextNodes, node0, rightNodes), leftNodes);
                    go_to_descendant(left, path0, node);
            }
        case right(path0):
            open tree(node0, contextNodes, subtreeNodes);
            open subtree(node0, ?parent, subtreeNodes);
            switch (subtreeNodes) {
                case empty:
                case tree(node00, leftNodes, rightNodes):
                    struct node *right = node0->right;
                    close context(right, node0, tcount(rightNodes), right_context(contextNodes, node0, leftNodes));
                    close tree(right, right_context(contextNodes, node0, leftNodes), rightNodes);
                    go_to_descendant(right, path0, node);
            }
    }
}

lemma void change_focus(struct node *node0, path path, struct node *node)
    requires tree(node0, ?contextNodes, ?subtreeNodes) &*& contains_at_path(combine(contextNodes, subtreeNodes), path, node) == true;
    ensures tree(node, get_context_nodes_at_path(root, combine(contextNodes, subtreeNodes), path), get_subtree_nodes_at_path(combine(contextNodes, subtreeNodes), path));
{
    go_to_root(contextNodes);
    assert tree(?rootNode, _, _);
    go_to_descendant(rootNode, path, node);
}

@*/

/*
  Natural Language Specification:
  - Description: Main function that demonstrates various operations on a binary tree, including adding nodes, retrieving parent nodes, and disposing of the tree.
  - Parameters: None.
  - Requires: No specific preconditions.
  - Ensures: No specific postconditions.
*/
int main() //@ : main
{
    struct node *root = create_tree();
    struct node *left = tree_add_left(root);
    struct node *leftRight = tree_add_right(left);
    struct node *leftRightParent = tree_get_parent(leftRight);

    struct node *leftLeft = tree_add_left(left);
 
    struct node *leftRightRight = tree_add_right(leftRight);

    tree_dispose(root);
    return 0;
}
