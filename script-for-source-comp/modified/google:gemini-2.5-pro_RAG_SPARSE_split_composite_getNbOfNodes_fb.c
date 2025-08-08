

struct Node {
  struct Node* left;
  struct Node* right;
  struct Node* parent;
  int count;
};



int internalGetNbOfNodes(struct Node* n)
{

  int c = n->count;

  return c;
}

int getNbOfNodes(struct Node* n)
{
    open isTree(n, value);
    int c = get_node_count(root, value, n);
    close isTree(n, value);
    return c;
}
