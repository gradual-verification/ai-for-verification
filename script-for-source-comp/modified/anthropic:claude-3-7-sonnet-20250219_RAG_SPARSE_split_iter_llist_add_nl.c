
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


void llist_add(struct llist *list, int x)
{
  struct node *l = 0;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  l = list->last;
  
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    list->first = n;
    list->last = n;
  } else {
    l->next = n;
    list->last = n;
    
  }
  
}

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


void llist_add(struct llist *list, int x)
{
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    list->first = n;
    list->last = n;
  } else {
    l->next = n;
    list->last = n;
    
    
  }
  
}

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


void llist_add(struct llist *list, int x)
{
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    list->first = n;
    list->last = n;
  } else {
    l->next = n;
    list->last = n;
    
  }
  
}

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


void llist_add(struct llist *list, int x)
{
  struct node *l = list->last;
  struct node *n = calloc(1, sizeof(struct node));
  if (n == 0) {
    abort();
  }
  
  n->next = 0;
  n->value = x;
  
  if (l == 0) {
    list->first = n;
  } else {
    l->next = n;
  }
  list->last = n;
  
  
  if (l == 0) {
  } else {
  }
  
}

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node
