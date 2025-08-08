

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};



struct Node* internalCreate(struct Node* parent)
{
  struct Node* n = malloc(sizeof(struct Node));
  if(n==0) {
    abort();
  } else {}
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
    fix(node);
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
  if(parent==0){
    open context(node, value, c);
    close context(node, value, c + 1);
  } else {
    open context(node, value, c);
    switch(value) {
        case Root:
        case lcontext(p, p_ctx, t_rhs):
            fix(p);
            close context(node, value, c + 1);
        case rcontext(p, t_lhs, p_ctx):
            fix(p);
            close context(node, value, c + 1);
    }
  }

}


struct Node* addLeft(struct Node* node)
