
struct heap_node {
    int value;
    struct heap_node *left;
    struct heap_node *right;
};


void heap_dispose(struct heap_node *node)
{
    if (node != 0) {
        struct heap_node *left = node->left;
        struct heap_node *right = node->right;
        heap_dispose(left);
        heap_dispose(right);
        free(node);
    } else {
    }
}
