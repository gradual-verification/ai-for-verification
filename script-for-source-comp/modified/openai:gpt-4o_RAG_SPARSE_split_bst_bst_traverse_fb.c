
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};


void bst_traverse(struct bst_node *node)
{
    if (node == 0) {
    } else {
        int val = node->value;
        struct bst_node *left = node->left;
        struct bst_node *right = node->right;
        bst_traverse(left);
        bst_traverse(right);
    }
}
