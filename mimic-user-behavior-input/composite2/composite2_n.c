#include "malloc.h"
#include <stdbool.h>

struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};

/*@

predicate subtree(struct node *root, struct node *parent, int count)
    requires
        root == 0 ?
            count == 0
        :
            root->left |-> ?left &*& root->right |-> ?right &*& root->parent |-> parent &*& root->count |-> count &*& malloc_block_node(root) &*&
            subtree(left, root, ?leftCount) &*& subtree(right, root, ?rightCount) &*& count == 1 + leftCount + rightCount;

predicate context(struct node *node, struct node *parent, int count)
    requires
        parent == 0 ?
            emp
        :
            parent->left |-> ?left &*& parent->right |-> ?right &*& parent->parent |-> ?grandparent &*& parent->count |-> ?parentCount &*& malloc_block_node(parent) &*&
            context(parent, grandparent, parentCount) &*&
            (node == left ? 
                 subtree(right, parent, ?rightCount) &*& parentCount == 1 + count + rightCount
             :
                 node == right &*& subtree(left, parent, ?leftCount) &*& parentCount == 1 + count + leftCount
            );

predicate tree(struct node *node)
    requires context(node, ?parent, ?count) &*& subtree(node, parent, count);

@*/

void abort();
    //@ requires true;
    //@ ensures false;
/**
 * Function: create_tree
 *
 * This function creates a new tree node and initializes its members.
 *
 * Outputs:
 * - Returns a pointer to the newly created node of type `struct node`.
 *
 * Behavior:
 * - The function allocates memory for a new node.
 * - If memory allocation fails (i.e., malloc returns 0), the function calls `abort` to terminate the program.
 * - If memory allocation is successful, the function initializes the following members of the node:
 *   - `left` to 0 (indicating no left child).
 *   - `right` to 0 (indicating no right child).
 *   - `parent` to 0 (indicating no parent).
 *   - `count` to 1 (initial count value for the node).
 * - The function then returns a pointer to the newly created and initialized node.
 */
struct node *create_tree()
  
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
/**
 * Function: subtree_get_count
 *
 * This function retrieves the count value of a given tree node.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns an integer representing the count value of the node.
 * - If the input node is null (0), the function returns 0.
 *
 * Behavior:
 * - The function initializes the result to 0.
 * - If the node pointer is not null, it sets the result to the count value of the node.
 * - Finally, it returns the result.
 */
int subtree_get_count(struct node *node)
   
{
    int result = 0;
    
    if (node == 0) {
    } else {
        result = node->count;
    }
    
    return result;
}
/**
 * Function: tree_get_count
 *
 * This function retrieves the count value of a given tree node by using the `subtree_get_count` function.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns an integer representing the count value of the node.
 * - If the input node is null (0), the function returns 0.
 *
 * Behavior:
 * - The function calls `subtree_get_count` with the input node to get the count value.
 * - It stores the result of this call in the variable `result`.
 * - Finally, it returns the result.
 */
int tree_get_count(struct node *node)
  
{
 
    int result = subtree_get_count(node);

    return result;
}
/**
 * Function: fixup_ancestors
 *
 * This function updates the count values of ancestors of a given node in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 * - parent: A pointer to the parent node of the input node.
 * - count: An integer representing the count value to be updated for the parent node.
 *
 * Behavior:
 * - If the parent node is null (0), the function does nothing.
 * - Otherwise, it updates the count value of the parent node based on the count values of its children and the provided count value.
 * - It then recursively calls itself to fix up the count values of the ancestors of the parent node.
 */

void fixup_ancestors(struct node *node, struct node *parent, int count)
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
/**
 * Function: tree_add_left
 *
 * This function adds a new node as the left child of a given node in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns a pointer to the newly added left child node.
 *
 * Behavior:
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 * - Otherwise, it allocates memory for a new node and initializes its members.
 * - If memory allocation fails (i.e., malloc returns 0), the function calls `abort` to terminate the program.
 * - If memory allocation is successful, it sets the parent of the new node to the input node and updates the count values of ancestors.
 * - Finally, it returns a pointer to the newly added left child node.
 */
struct node *tree_add_left(struct node *node)
{
   
    if (node == 0) {
        abort();
    }
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
            if (nodeLeft != 0) {
                abort();
            }
            
            node->left = n;
            
            fixup_ancestors(n, node, 1);
        }
        
        return n;
    }
}
/**
 * Function: tree_add_right
 *
 * This function adds a new node as the right child of a given node in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns a pointer to the newly added right child node.
 *
 * Behavior:
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 * - Otherwise, it allocates memory for a new node and initializes its members.
 * - If memory allocation fails (i.e., malloc returns 0), the function calls `abort` to terminate the program.
 * - If memory allocation is successful, it sets the parent of the new node to the input node and updates the count values of ancestors.
 * - Finally, it returns a pointer to the newly added right child node.
 */
struct node *tree_add_right(struct node *node)
{
    
    if (node == 0) {
        abort();
    }
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
            if (nodeRight != 0) {
                abort();
            }
         
            node->right = n;
          
            fixup_ancestors(n, node, 1);
        }
        
        return n;
    }
}
/**
 * Function: tree_get_parent
 *
 * This function retrieves the parent node of a given node in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns a pointer to the parent node of the input node.
 * - If the input node is null (0) or its parent is null (0), the function calls `abort` to terminate the program.
 *
 * Behavior:
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 * - Otherwise, it retrieves the parent node of the input node.
 * - If the parent node is null (0), indicating that the input node is the root, the function calls `abort` to terminate the program.
 * - Finally, it returns a pointer to the parent node.
 */
struct node *tree_get_parent(struct node *node)
{
 
    if (node == 0) {
        abort();
    }
    {
        struct node *parent = node->parent;
        if (parent == 0) {
            abort();
        }
        
        return parent;
    }
}
/**
 * Function: tree_get_left
 *
 * This function retrieves the left child node of a given node in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns a pointer to the left child node of the input node.
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 *
 * Behavior:
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 * - Otherwise, it retrieves the left child node of the input node.
 * - Finally, it returns a pointer to the left child node.
 */
struct node *tree_get_left(struct node *node)
{
    
    if (node == 0) {
        abort();
    }
    {
        struct node *left = node->left;
      
        return left;
    }
}
/**
 * Function: tree_get_right
 *
 * This function retrieves the right child node of a given node in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns a pointer to the right child node of the input node.
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 *
 * Behavior:
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 * - Otherwise, it retrieves the right child node of the input node.
 * - Finally, it returns a pointer to the right child node.
 */
struct node *tree_get_right(struct node *node)
  
{
 
    if (node == 0) {
        abort();
    }
    {
        struct node *right = node->right;
      
        return right;
    }
}
/**
 * Function: tree_has_parent
 *
 * This function checks whether a given node has a parent in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns true if the input node has a parent, false otherwise.
 *
 * Behavior:
 * - Initializes the result to false.
 * - If the input node is not null (0), it retrieves the parent node of the input node.
 * - Updates the result based on whether the parent node is not null.
 * - Finally, it returns the result.
 */
bool tree_has_parent(struct node *node)
    
{
    
    bool result = false;
    if (node == 0) {
    } else {
        struct node *parent = node->parent;
        result = parent != 0;
    }
    
    return result;
}
/**
 * Function: tree_has_left
 *
 * This function checks whether a given node has a left child in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns true if the input node has a left child, false otherwise.
 *
 * Behavior:
 * - Initializes the result to false.
 * - If the input node is not null (0), it retrieves the left child node of the input node.
 * - Updates the result based on whether the left child node is not null.
 * - Finally, it returns the result.
 */
bool tree_has_left(struct node *node)
  
{

    bool result = false;
    if (node == 0) {
    } else {
        struct node *left = node->left;
        result = left != 0;
    }
   
    return result;
}
/**
 * Function: tree_has_right
 *
 * This function checks whether a given node has a right child in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Outputs:
 * - Returns true if the input node has a right child, false otherwise.
 *
 * Behavior:
 * - Initializes the result to false.
 * - If the input node is not null (0), it retrieves the right child node of the input node.
 * - Updates the result based on whether the right child node is not null.
 * - Finally, it returns the result.
 */
bool tree_has_right(struct node *node)
   
{
   
    bool result = false;
    if (node == 0) {
    } else {
        struct node *right = node->right;
        result = right != 0;
    }
   
    return result;
}
/**
 * Function: dispose_node
 *
 * This function disposes of a given node and its descendants in a tree structure.
 *
 * Inputs:
 * - node: A pointer to a tree node of type `struct node`.
 *
 * Behavior:
 * - If the input node is null (0), the function does nothing.
 * - Otherwise, it recursively disposes of the left and right child nodes of the input node.
 * - After disposing of all descendants, it frees the memory allocated for the input node.
 */
void dispose_node(struct node *node) 
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
/**
 * Function: tree_dispose
 *
 * This function disposes of a given tree by freeing memory allocated for all its nodes.
 *
 * Inputs:
 * - node: A pointer to the root node of the tree.
 *
 * Behavior:
 * - If the input node is null (0), the function calls `abort` to terminate the program.
 * - Otherwise, it checks if the input node has a parent. If it does, it calls `abort` to terminate the program, ensuring that the input node is the root.
 * - Finally, it calls the `dispose_node` function to recursively dispose of all nodes in the tree starting from the root node.
 */
void tree_dispose(struct node *node)
{
    if (node == 0) {
        abort();
    }

    {
        struct node *parent = node->parent;
        if (parent != 0) {
            abort();
        }
       
    }
    dispose_node(node);
}

int main()
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
