
struct node {
    struct node *left;
    struct node *right;
    struct node *parent;
    int count;
};


int subtree_get_count(struct node *node)
{
    int result = 0;
    if (node == 0) {
    } else {
        result = node->count;
    }
    return result;
}


void fixup_ancestors(struct node *node, struct node *parent, int count)
{
    if (parent == 0) {
    } else {
        struct node *left = parent->left;
        struct node *right = parent->right;
        struct node *grandparent = parent->parent;
        int leftCount = 0;
        int rightCount = 0;
        if (node == left && node != right) {
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else if (node == right && node != left) {
            leftCount = subtree_get_count(left);
            rightCount = count;
        } else if (node == left && node == right) { // implies node == 0
            leftCount = count;
            rightCount = subtree_get_count(right);
        } else {
            abort();
        }
        if (rightCount < 0 || leftCount > INT_MAX - 1 - rightCount) { abort();}
        int parentCount = 1 + leftCount + rightCount;
        parent->count = parentCount;
        
        
        fixup_ancestors(parent, grandparent, parentCount);
        
    }
}


struct node *tree_add_left(struct node *node)
{
    if (node == 0) {
        abort(); // Unreachable under this contract
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
                abort(); // Unreachable, node_pred requires node->left |-> 0
            }
            node->left = n;
            if (n == node->right) {
                abort(); // Unreachable, n is a fresh pointer
            }
            fixup_ancestors(n, node, 1);
        }
        return n;
    }
}
