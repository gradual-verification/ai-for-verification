#include "stdlib.h"

struct node {
 struct node* next;
 int value;
};

struct list {
 struct node* head;
};

/*@
predicate lseg(struct node* from, struct node* to)
 requires from == to ? true : 
 from->next |-> ?next &*& from->value |-> ?val &*& malloc_block_node(from) &*& lseg(next, to);

predicate list(struct list* l)
 requires l->head |-> ?head &*& lseg(head,0) &*& malloc_block_list(l);

lemma_auto void lseg_zero()
 requires lseg(?from, ?to);
 ensures lseg(from, to) &*& true && (from == to) == (to == 0);
{
 open lseg(from, to);
}

lemma void lseg_append(struct node* a, struct node* b)
 requires lseg(a, ?b, ?vs1) &*& b !=0 &*& b->next |-> ?n &*& b->value |-> ?v &*& malloc_block_node(b) &*& lseg(n,0, ?vs2);
 ensures lseg(a, n, append(vs1, cons(v, nil))) &*& lseg(n,0, vs2);
{
 if(a == b) {
 } else {
 lseg_append(a->next, b);
 }
 open lseg(n,0, vs2);
}
@*/

struct list* create_list()
 //@ requires true;
 //@ ensures list(result);
{
 struct list* l = malloc(sizeof(struct list));
 if(l ==0) { abort(); }
 l->head =0;
 //@ close lseg(0,0);
 //@ close list(l);
 return l;
}

void add(struct list* l, int x)
 //@ requires list(l);
 //@ ensures list(l);
{
 //@ open list(l);
 struct node* h = add_helper(l->head, x);
 l->head = h;
 //@ close list(l);
}

struct node* add_helper(struct node* n, int x)
 //@ requires lseg(n,0);
 //@ ensures lseg(result,0);
{
 //@ open lseg(n,0);
 struct node* newNode =0;
 if(n ==0) {
 newNode = malloc(sizeof(struct node));
 if(newNode ==0) { abort(); }
 newNode->value = x;
 newNode->next =0;
 //@ close lseg(0,0);
 } else {
 struct node* tmp = add_helper(n->next, x);
 n->next = tmp;
 newNode = n;
 }
 //@ close lseg(newNode,0);
 return newNode;
}

int list_length(struct list* l) 
 //@ requires list(l);
 //@ ensures list(l) &*& result == 0;
{
 //@ open list(l);
 int myLength = list_length_helper(l->head);
 //@ close list(l);
 return myLength;
}

int list_length_helper(struct node* n) 
 //@ requires lseg(n,0);
 //@ ensures lseg(n,0) &*& result == 0;
{
 //@ open lseg(n,0);
 if(n ==0) {
 //@ close lseg(0,0);
 return0;
 } else {
 int tmp = list_length_helper(n->next);
 //@ close lseg(n,0);
 return tmp +1;
 }
}

void dispose(struct list* l) 
 //@ requires list(l);
 //@ ensures true;
{
 //@ open list(l);
 struct node* current = l->head;
 while(current !=0) 
 //@ invariant lseg(current,0); 
 {
 //@ open lseg(current,0);
 struct node* oldcurrent = current;
 current = current->next;
 free(oldcurrent);
 }
 //@ open lseg(0,0);
 free(l);
}

int main()
 //@ requires true;
 //@ ensures true;
{
 struct list* l= create_list();
 add(l,1);
 add(l,2);
 add(l,2);
 add(l,4);
  
 int tmp = list_length(l);
  
 //@ assert tmp ==4;
  
 dispose(l);
 return0;
}