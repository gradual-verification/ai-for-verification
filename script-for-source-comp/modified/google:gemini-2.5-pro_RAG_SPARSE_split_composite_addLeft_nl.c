    predicate tree(struct Node *n; int count, struct Node *p) =
        n == 0 ?
            count == 0
        :
            n->left |-> ?l &*& n->right |-> ?r &*& n->parent |-> p &*& n->count |-> count &*& malloc_block_Node(n) &*&
            tree(l, ?lc, n) &*& tree(r, ?rc, n) &*&
            count == 1 + lc + rc;
    predicate node_and_subtrees(struct Node *n; struct Node *p, int correct_count) =
        n == 0 ?
            correct_count == 0
        :
            ... n->count |-> _ &*& ...
            tree(n->left, ?lc, n) &*& tree(n->right, ?rc, n) &*&
            correct_count == 1 + lc + rc;
    predicate path_counts_off_by_one(struct Node *n) =
        n == 0 ?
            true
        :
            node_and_subtrees(n, ?p, ?correct_count) &*&
            n->count |-> correct_count - 1 &*&
            path_counts_off_by_one(p);
    predicate path_counts_correct(struct Node *n) =
        n == 0 ?
            true
        :
            node_and_subtrees(n, ?p, ?correct_count) &*&
            n->count |-> correct_count &*&
            path_counts_correct(p);


struct Node {
    struct Node* left;
    struct Node* right;
    struct Node* parent;
    int count;
};


struct Node* create()
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->parent = 0;
    n->left = 0;
    n->right = 0;
    n->count = 1;
    
    return n;
}


struct Node* internalCreate(struct Node* parent)
{
    struct Node* n = malloc(sizeof(struct Node));
    if(n == 0) {
        abort();
    }
    n->left = 0;
    n->right = 0;
    n->parent = parent;
    n->count = 1;

    return n;
}


struct Node* internalAddLeft(struct Node* node)
{
    
    struct Node* child = internalCreate(node);
    
    node->left = child;
    
    
    
    fix_lemma(node);
    
    path_to_tree_lemma(node);
    
    
    return child;
}


void fix(struct Node* node)
{
    
    int tmp = node->count;
    if (tmp == INT_MAX) {
        abort();
    }
    node->count = tmp + 1;

    struct Node* parent = node->parent;
    if(parent != 0) {
        fix(parent);
    } else {
    }
    
}


struct Node* addLeft(struct Node* node)
{
    
    struct Node* newChild = internalAddLeft(node);
    
    
    return newChild;
}
