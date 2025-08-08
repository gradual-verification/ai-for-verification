
struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};





struct iter {
    struct node *current;
};




void iter_dispose(struct iter *i)
{
    open iter(i, f1, l, v0, v);
    
    free(i);
    
    producing_lemma_from_predicate(llist_with_node, llist_with_node_to_llist_lemma)();
    
}
