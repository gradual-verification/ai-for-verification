#include "stdlib.h"
//@ #include "maps.gh"

struct node {
  void* val;
  struct node* next;
};

struct set {
  struct node* head;
};

/*@
predicate lseg(struct node* first, struct node* last, list<void*> vs) =
  first == last ?
    vs == nil
  :
    first->val |-> ?val &*& first->next |-> ?next &*& malloc_block_node(first) &*& lseg(next, last, ?tail);

predicate set(struct set* set) =
  set->head |-> ?head &*& malloc_block_set(set) &*& lseg(head, 0, _);
@*/


struct set* create_set()
  //@ requires true;
  //@ ensures result == 0 ? true : set(result);
{
  struct set* set = malloc(sizeof(struct set));
  if(set == 0) return 0;
  set->head = 0;
 
  return set;
}


void set_add(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set);
{

  struct node* n = malloc(sizeof(struct node));
  if(n == 0) abort();
  n->next = set->head;
  n->val = x;
  set->head = n;

}


bool set_contains(struct set* set, void* x)
  //@ requires set(set);
  //@ ensures set(set) &*& result ? true : true;
{

  struct node* curr = set->head;
  bool found = false;
  while(curr != 0 && !found) 
 
  {
    
    if(curr->val == x) {
      found = true;
    }
    curr = curr->next;
   
  }

  return found;
}

void set_dispose(struct set* set)
  //@ requires set(set);
  //@ ensures true;
{

  struct node* curr = set->head;
  while(curr != 0) 
  {
  
    struct node* nxt = curr->next;
    free(curr);
    curr = nxt;
  }

  free(set);
}


int main() //@ : main
  //@ requires true;
  //@ ensures true;
{
  struct set* set = create_set();
  if(set == 0) return 0;
  set_add(set, (void*) 1);
  set_add(set, (void*) 2);
  set_add(set, (void*) 3);
  bool cnt = set_contains(set, (void*) 1);
  assert(cnt);
  set_dispose(set);
  return 0;
}
