
struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};




struct node *tree_get_left(struct node *node)
{
    if (node == 0) {
        abort();
    }
    
    struct node *left = node->left;
    
    
    if (left == 0) {
        return left;
    } else {
        
        
        
        return left;
    }
}
