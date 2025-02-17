#include "stdlib.h"

struct node {
  struct node* next;
  int value;
};

struct stack {
  struct node* head;
};

/*@
predicate lseg(struct node* f, struct node* t; list<int> vs) =
  f == t ? vs == nil : f != 0 &*& f->value |-> ?v &*& f->next |-> ?n &*& lseg(n, t, ?vs0) &*& vs == cons(v, vs0);

predicate stack(struct stack* s; list<int> vs) =
  s->head |-> ?h &*& lseg(h, 0, vs);
  
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

int pop(struct stack* s)
  //@ requires stack(s, ?vs) &*& vs != nil;
  //@ ensures stack(s, tail(vs)) &*& result == head(vs);
{
  struct node* tmp = s->head;
  int res = tmp->value;
  s->head = tmp->next;
  free(tmp);
  return res;
}

void dispose(struct stack* s) 
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


int get_length(struct stack* s) 
  //@ requires stack(s, ?vs);
  //@ ensures stack(s, vs) &*& result == length(vs);
{
  int r = 0;

  struct node* n = s->head;
  while(n != 0) 

  {
    r = r + 1;
    n = n->next;
 
  }
  return r;
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct stack* s = create_stack();
  push(s, 1);
  push(s, 2);
  push(s, 3);
  int r1 = pop(s);
  int r2 = pop(s);
  int r3 = pop(s);

  dispose(s);
  return 0;
}