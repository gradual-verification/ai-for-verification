
struct bst_node {
    struct bst_node *left;
    struct bst_node *right;
    int value;
};


struct bst_node *bst_create()
{
    return 0;
}

struct bst_node *bst_insert(struct bst_node *node, int value)
{
    if (node == 0) {
        struct bst_node *new_node = malloc(sizeof(struct bst_node));
        if (new_node == 0) abort();
        new_node->value = value;
        new_node->left = 0;
        new_node->right = 0;
        return new_node;
    } else {
        if (value < node->value) {
            node->left = bst_insert(node->left, value);
        } else if (value > node->value) {
            node->right = bst_insert(node->right, value);
        } else {
        }
        return node;
    }
}

bool bst_search(struct bst_node *node, int value)
{
    if (node == 0) {
        return false;
    }
    if (node->value == value) {
        return true;
    }
    else if (value < node->value) {
        bool res = bst_search(node->left, value);
        return res;
    }
    else {
        bool res = bst_search(node->right, value);
        return res;
    }
}

void bst_traverse(struct bst_node *node)
{
    if (node == 0) {
    } else {
        int val = node->value;
        bst_traverse(node->left);
        bst_traverse(node->right);
    }
}

void bst_dispose(struct bst_node *node)
{
    if (node != 0) {
        bst_dispose(node->left);
        bst_dispose(node->right);
        free(node);
    } else {
    }
}

int main()
{
    struct bst_node *tree = bst_create();
    tree = bst_insert(tree, 10);
    tree = bst_insert(tree, 5);
    tree = bst_insert(tree, 15);
    tree = bst_insert(tree, 8);
    tree = bst_insert(tree, 12);

    bool found8 = bst_search(tree, 8);
    
    bool found20 = bst_search(tree, 20);

    bst_traverse(tree);

    bst_dispose(tree);
    return 0;
}
