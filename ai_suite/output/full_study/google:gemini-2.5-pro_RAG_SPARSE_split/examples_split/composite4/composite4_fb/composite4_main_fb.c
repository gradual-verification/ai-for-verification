#include "stdlib.h"

struct node {
  struct node *left;
  struct node *right;
  struct node *parent;
  int count;
};

/*@

inductive tree =
    empty
  | tree(struct node *, tree, tree);

fixpoint int tcount(tree nodes) {
  switch (nodes) {
    case empty: return 0;
    case tree(root, left, right):
      return 1 + tcount(left) + tcount(right);
  }
}

predicate subtree(struct node * root, struct node * parent, tree t) =
  switch (t) {
    case empty: return root == 0;
    case tree(root0, leftNodes, rightNodes):
      return
        root == root0 &*&
        root->left |-> ?left &*&
        root->right |-> ?right &*&
        root->parent |-> parent &*&
        root->count |-> tcount(t) &*&
        subtree(left, root, leftNodes) &*&
        subtree(right, root, rightNodes);
  };

inductive context =
    root
  | left_context(context, struct node *, tree)
  | right_context(context, struct node *, tree);

predicate context(struct node * node, struct node * parent,
                  int count, context nodes) =
  switch (nodes) {
    case root: return parent == 0;
    case left_context(pns, parent0, rightNodes):
      return
        parent == parent0 &*&
        parent->left |-> node &*&
        parent->right |-> ?right &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        context(parent, gp, pcount, pns) &*&
        subtree(right, parent, rightNodes) &*&
        pcount == 1 + count + tcount(rightNodes);
    case right_context(pns, parent0, leftNodes):
      return
        parent == parent0 &*&
        parent->left |-> ?left &*&
        parent->right |-> node &*&
        parent->parent |-> ?gp &*&
        parent->count |-> ?pcount &*&
        context(parent, gp, pcount, pns) &*&
        subtree(left, parent, leftNodes) &*&
        pcount == 1 + tcount(leftNodes) + count;
  };

predicate tree(struct node * node, context c, tree subtree) =
  context(node, ?parent, tcount(subtree), c) &*&
  subtree(node, parent, subtree);

lemma void switch_focus_left_to_right(struct node *l, struct node *r)
    requires tree(l, left_context(?gpc, ?gp, tree(r, ?rtl, ?rtr)), ?lt);
    ensures tree(r, right_context(gpc, gp, lt), tree(r, rtl, rtr));
{
    open tree(l, left_context(gpc, gp, tree(r, rtl, rtr)), lt);
    open context(l, _, _, left_context(gpc, gp, tree(r, rtl, rtr)));
    close context(r, gp, 1 + tcount(lt) + tcount(tree(r, rtl, rtr)), right_context(gpc, gp, lt));
    close tree(r, right_context(gpc, gp, lt), tree(r, rtl, rtr));
}

fixpoint tree build_whole_tree(context c, tree t) {
    switch(c) {
        case root: return t;
        case left_context(pc, p, rt): return build_whole_tree(pc, tree(p, t, rt));
        case right_context(pc, p, lt): return build_whole_tree(pc, tree(p, lt, t));
    }
}

fixpoint struct node* get_root(struct node* n, context c) {
    switch(c) {
        case root: return n;
        case left_context(pc, p, rt): return get_root(p, pc);
        case right_context(pc, p, lt): return get_root(p, pc);
    }
}

lemma void tree_unfocus_lemma(struct node* n, context c, tree t)
    requires context(n, ?p, _, c) &*& subtree(n, p, t);
    ensures tree(get_root(n, c), root, build_whole_tree(c, t));
{
    switch(c) {
        case root:
            open context(n, _, _, c);
            close tree(n, root, t);
            break;
        case left_context(pc, p_node, rt):
            open context(n, _, _, c);
            close subtree(p_node, _, tree(p_node, t, rt));
            tree_unfocus_lemma(p_node, pc, tree(p_node, t, rt));
            break;
        case right_context(pc, p_node, lt):
            open context(n, _, _, c);
            close subtree(p_node, _, tree(p_node, lt, t));
            tree_unfocus_lemma(p_node, pc, tree(p_node, lt, t));
            break;
    }
}

lemma void tree_unfocus(struct node* n, struct node* root_node)
    requires tree(n, ?c, ?t) &*& root_node == get_root(n, c);
    ensures tree(root_node, root, build_whole_tree(c, t));
{
    open tree(n, c, t);
    tree_unfocus_lemma(n, c, t);
}

@*/


struct node * create_node(struct node * p)
  //@ requires true;
  /*@ ensures 
       subtree(result, p, tree(result, empty, empty));
  @*/
{
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->left = 0;
  n->right = 0;
  n->parent = p;
  n->count = 1;
  return n;
}


struct node *create_tree()
  //@ requires true;
  /*@ ensures
       tree(result, root, tree(result, empty, empty));
  @*/
{
  struct node *n = create_node(0);
  //@ close context(n, 0, 1, root);
  //@ close tree(n, root, tree(n, empty, empty));
  return n;
}


int subtree_get_count(struct node *node)
  //@ requires subtree(node, ?parent, ?nodes);
  /*@ ensures subtree(node, parent, nodes) &*&
              result == tcount(nodes) &*& 0 <= result; @*/
{
  //@ open subtree(node, parent, nodes);
  int result = 0;
  if (node != 0) { result = node->count; }
  //@ close subtree(node, parent, nodes);
  return result;
}


void fixup_ancestors(struct node * n, struct node * p, int count)
  //@ requires context(n, p, _, ?c) &*& 0 <= count;
  //@ ensures context(n, p, count, c);
{
  //@ open context(n, p, _, c);
  if (p == 0) {
    //@ close context(n, p, count, c);
  } else {
    struct node *left = p->left;
    struct node *right = p->right;
    struct node *grandparent = p->parent;
    int leftCount = 0;
    int rightCount = 0;
    if (n == left) {
      leftCount = count;
      //@ open subtree(right, p, _);
      rightCount = subtree_get_count(right);
      //@ close subtree(right, p, _);
    } else {
      //@ open subtree(left, p, _);
      leftCount = subtree_get_count(left);
      //@ close subtree(left, p, _);
      rightCount = count;
    }
    if (INT_MAX - 1 - leftCount < rightCount) {
      abort();
    }
    {
      int pcount = 1 + leftCount + rightCount;
      p->count = pcount;
      fixup_ancestors(p, grandparent, pcount);
      //@ close context(n, p, count, c);
    }
  }
}


struct node *tree_add_left(struct node *node)
  /*@ requires
        tree(node, ?c, ?t) &*&
        switch (t) {
          case empty: return false;
          case tree(n0, l, r): return l == empty;
        }; @*/
  /*@ ensures
        switch (t) {
          case empty: return false;
          case tree(n0, l, r): return
            tree(result, left_context(c, node, r),
              tree(result, empty, empty));
        };
  @*/
{
  struct node *n = create_node(node);
  {
      //@ open tree(node, c, t);
      //@ open subtree(node, _, t);
      struct node *nodeLeft = node->left;
      node->left = n;
      //@ close subtree(node, _, t);
      //@ open context(node, _, _, c);
      fixup_ancestors(n, node, 1);
      //@ close tree(result, left_context(c, _, _), tree(result, empty, empty));
  }
  return n;
}


struct node *tree_add_right(struct node *node)
    /*@ requires
            tree(node, ?contextNodes, ?subtreeNodes) &*&
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes): return rightNodes == empty;
            };
    @*/
    /*@ ensures
            switch (subtreeNodes) {
                case empty: return false;
                case tree(node0, leftNodes, rightNodes):
                    return tree(result, right_context(contextNodes, node, leftNodes), tree(result, empty, empty));
            };
    @*/
{
    struct node *n = create_node(node);
    {
        //@ open tree(node, contextNodes, subtreeNodes);
        //@ open subtree(node, _, subtreeNodes);
        struct node *nodeRight = node->right;
        node->right = n;
        //@ close subtree(node, _, subtreeNodes);
        //@ open context(node, _, _, contextNodes);
        fixup_ancestors(n, node, 1);
        //@ close tree(result, right_context(contextNodes, _, _), tree(result, empty, empty));
    }
    return n;
}


struct node *tree_get_parent(struct node *node)
  /*@ requires tree(node, ?c, ?t) &*&
        c != root &*& t != empty; @*/
  /*@ ensures
        switch (c) {
          case root: return false;
          case left_context(pns, p, r):
            return result == p &*&
              tree(p, pns, tree(p, t, r));
          case right_context(pns, p, l):
            return result == p &*&
              tree(p, pns, tree(p, l, t));
        }; @*/
{
  //@ open tree(node, c, t);
  //@ open context(node, _, _, c);
  struct node *p = node->parent;
  //@ switch(c) { case root: case left_context(pns, p0, r): case right_context(pns, p0, l): }
  //@ close subtree(p, _, tree(p, _, _));
  //@ close tree(p, _, tree(p, _, _));
  return p;
}


void subtree_dispose(struct node *node)
  //@ requires subtree(node, _, _);
  //@ ensures true;
{
  //@ open subtree(node, _, _);
  if (node != 0) {
    {
      struct node *left = node->left;
      subtree_dispose(left);
    }
    {
      struct node *right = node->right;
      subtree_dispose(right);
    }
    free(node);
  }
}


void tree_dispose(struct node *node)
  //@ requires tree(node, root, ?t);
  //@ ensures true;
{
  //@ open tree(node, root, t);
  //@ open context(node, ?p, _, root);
  subtree_dispose(node);
}


// TODO: make this function pass the verification
int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct node *root = create_tree();
    struct node *left = tree_add_left(root);
    struct node *leftRight = tree_add_right(left);
    struct node *leftRightParent = tree_get_parent(leftRight);
    struct node *leftLeft = tree_add_left(left);
    
    //@ switch_focus_left_to_right(leftLeft, leftRight);
    
    struct node *leftRightRight = tree_add_right(leftRight);
    
    //@ tree_unfocus(leftRightRight, root);
    
    tree_dispose(root);
    return 0;
}