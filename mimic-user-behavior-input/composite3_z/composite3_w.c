#include "malloc.h"
#include <stdbool.h>

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

inductive tree = nil | tree(struct node *, tree, tree);

fixpoint int count(tree nodes) {
    switch (nodes) {
        case nil: return 0;
        case tree(root, leftNodes, rightNodes): return 1 + count(leftNodes) + count(rightNodes);
    }
}

predicate subtree(struct node *root, struct node *parent, tree nodes)
    requires
        switch (nodes) {
            case nil: return root == 0;
            case tree(root0, leftNodes, rightNodes):
                return
                    root == root0 &*& root != 0 &*&
                    root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> count(nodes) &*& 
                    subtree(left, root, leftNodes) &*& subtree(right, root, rightNodes);
        };

inductive context = root | left_context(context, struct node *, tree) | right_context(context, struct node *, tree);

predicate context(struct node *node, struct node *parent, int count, context nodes)
    requires
        switch (nodes) {
            case root: return parent == 0;
            case left_context(parentContextNodes, parent0, rightNodes):
                return
                    parent == parent0 &*& parent != 0 &*&
                    parent->left |-> node &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount  &*&
                    context(parent, grandparent, parentCount, parentContextNodes) &*& subtree(right, parent, rightNodes) &*&
                    parentCount == 1 + count + count(rightNodes);
            case right_context(parentContextNodes, parent0, leftNodes):
                return
                    parent == parent0 &*& parent != 0 &*&
                    parent->left |-> ?left &*& parent->right |-> node &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount  &*&
                    context(parent, grandparent, parentCount, parentContextNodes) &*& subtree(left, parent, leftNodes) &*&
                    parentCount == 1 + count(leftNodes) + count;
        };

predicate tree(struct node *node, context contextNodes, tree subtreeNodes)
    requires context(node, ?parent, count(subtreeNodes), contextNodes) &*& subtree(node, parent, subtreeNodes);

@*/

void abort();
    //@ requires true;
    //@ ensures false;

struct node *create_tree()
    //@ requires true;
    //@ ensures tree(result, root, tree(result, nil, nil));
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
 
    n->right = 0;
    
    n->parent = 0;
    n->count = 1;
   
    return n;
}

int subtree_get_count(struct node *node)
    //@ requires subtree(node, ?parent, ?nodes);
    //@ ensures subtree(node, parent, nodes) &*& result == count(nodes);
{
    int result = 0;

    if (node == 0) {
    } else {
        result = node->count;
    }

    return result;
}

int tree_get_count(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes);
    //@ ensures tree(node, contextNodes, subtreeNodes) &*& result == count(subtreeNodes);
{
    
    int result = subtree_get_count(node);
    
    return result;
}

void fixup_ancestors(struct node *node, struct node *parent, int count)
    //@ requires context(node, parent, _, ?contextNodes);
    //@ ensures context(node, parent, count, contextNodes);
{
    
    if (parent == 0) {
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left) {
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else {
            leftCount = subtree_get_count(left);
            rightCount = count;
        }
        {
            int parentCount = 1 + leftCount + rightCount;
            parent->count = parentCount;
            fixup_ancestors(parent, grandparent, parentCount);
        }
    }

}

struct node *tree_add_left(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes): return leftNodes == nil;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, left_context(contextNodes, node, rightNodes), tree(result, nil, nil));
            };
    @*/
{
    
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
   
    n->right = 0;
   
    n->parent = node;
    n->count = 1;
  
    {
        struct node *nodeLeft = node->left;
        //@ open subtree(nodeLeft, node, nil);
        node->left = n;
        //@ close context(n, node, 0, left_context(contextNodes, node, rightNodes));
        fixup_ancestors(n, node, 1);
    }
   
    return n;
}

struct node *tree_add_right(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes): return rightNodes == nil;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, right_context(contextNodes, node, leftNodes), tree(result, nil, nil));
            };
    @*/
{
    
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) {
        abort();
    }
    n->left = 0;
   
    n->right = 0;
   
    n->parent = node;
    n->count = 1;

    {
        struct node *nodeRight = node->right;
       
        node->right = n;
       
        fixup_ancestors(n, node, 1);
    }
    
    return n;
}

struct node *tree_get_parent(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*& contextNodes != root &*& subtreeNodes != nil;
    @*/
    /*@ ensures
            switch (contextNodes) {
                case root: return false;
                case left_context(parentContextNodes, parent, rightNodes):
                    return result == parent &*& tree(parent, parentContextNodes, tree(parent, subtreeNodes, rightNodes));
                case right_context(parentContextNodes, parent, leftNodes):
                    return result == parent &*& tree(parent, parentContextNodes, tree(parent, leftNodes, subtreeNodes));
            };
    @*/
{
    
    struct node *parent = node->parent;
   
    return parent;
}

struct node *tree_get_left(struct node *node)
    /*@ requires tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes): return leftNodes != nil;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, left_context(contextNodes, node, rightNodes), leftNodes);
            };
    @*/
{

    struct node *left = node->left;

    return left;
}

struct node *tree_get_right(struct node *node)
    /*@ requires tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes): return rightNodes != nil;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes):
                   return tree(result, right_context(contextNodes, node, leftNodes), rightNodes);
            };
    @*/
{
  
    struct node *right = node->right;

    return right;
}

bool tree_has_parent(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != nil;
    //@ ensures tree(node, contextNodes, subtreeNodes) &*& result == (contextNodes != root);
{
    
    struct node *parent = node->parent;

    return parent != 0;
}

bool tree_has_left(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != nil;
    /*@ ensures
            tree(node, contextNodes, subtreeNodes) &*&
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes): return result == (leftNodes != nil);
            };
    @*/
{

    struct node *left = node->left;
  
    return left != 0;
}

bool tree_has_right(struct node *node)
    //@ requires tree(node, ?contextNodes, ?subtreeNodes) &*& subtreeNodes != nil;
    /*@ ensures
            tree(node, contextNodes, subtreeNodes) &*&
            switch (subtreeNodes) {
                case nil: return false;
                case tree(node0, leftNodes, rightNodes): return result == (rightNodes != nil);
            };
    @*/
{
    
    struct node *right = node->right;

    return right != 0;
}

void dispose_node(struct node *node)
    //@ requires subtree(node, _, _);
    //@ ensures emp;
{

    if (node == 0) {
    } else {
        {
            struct node *left = node->left;
            dispose_node(left);
        }
        {
            struct node *right = node->right;
            dispose_node(right);
        }
        free(node);
    }
}

void tree_dispose(struct node *node)
    //@ requires tree(node, root, _);
    //@ ensures emp;
{

    dispose_node(node);
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct node *node0 = create_tree();
    struct node *node = node0;
    node = tree_add_left(node);
    node = tree_add_right(node);
    node = tree_get_parent(node);
    node = tree_add_left(node);
    node = tree_get_parent(node);
    node = tree_get_parent(node);
    //@ assert(node == node0);
    tree_dispose(node);
    return 0;
}
