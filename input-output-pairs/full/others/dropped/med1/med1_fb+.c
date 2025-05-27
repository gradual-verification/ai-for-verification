#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct stack {
  struct node* head;
};

/*@

predicate linked(struct node* f, struct node* t; list<int> vs) =
  f == t ? vs == nil : 
  f != 0 &*& f->value |-> ?v &*& f->next |-> ?n &*& 
  malloc_block_node(f) &*& linked(n, t, ?vs0) &*& vs == cons(v, vs0);

predicate stack(struct stack* s; list<int> vs) =
  s->head |-> ?h &*& linked(h, 0, vs) &*& malloc_block_stack(s);
  
@*/

struct stack* create_stack() 
  //@ requires true;
  //@ ensures stack(result, nil);
{
  struct stack* s = malloc(sizeof(struct stack));
  if(s == 0) abort();
  s->head = 0;
  return s;
}


void push(struct stack* s, int x)
  //@ requires stack(s, ?vs);
  //@ ensures stack(s, cons(x, vs));
{
  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = s->head;
  n->value = x;
  s->head = n;
}

void clear(struct stack* s) 
  //@ requires stack(s, ?vs);
  //@ ensures true;
{
  struct node* n = s->head;
  while(n != 0) 
  {
    struct node* tmp = n;
    n = n->next;
    free(tmp);
  }
  free(s);
}



int main()
  //@ requires true;
  //@ ensures true;
{
  struct stack* s = create_stack();
  push(s, 1);
  clear(s);
  return 0;
}