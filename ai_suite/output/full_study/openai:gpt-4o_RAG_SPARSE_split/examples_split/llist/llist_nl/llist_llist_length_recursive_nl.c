#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct llist {
  struct node *first;
  struct node *last;
};

/*@
predicate lseg(struct node *first, struct node *last, list<int> values) =
  first == last ? 
    values == nil 
  : 
    first->value |-> ?v &*& first->next |-> ?n &*& malloc_block_node(first) &*& lseg(n, last, ?vs) &*& values == cons(v, vs);

predicate llist(struct llist *l, list<int> values) =
  l->first |-> ?f &*& l->last |-> ?la &*& malloc_block_llist(l) &*& lseg(f, la, values);
@*/

/*@
lemma void lseg_to_nil(struct node *n)
  requires lseg(n, n, ?vs);
  ensures vs == nil;
{
  open lseg(n, n, vs);
  close lseg(n, n, vs);
}

lemma void lseg_to_lseg(struct node *n1, struct node *n2)
  requires lseg(n1, n2, ?vs);
  ensures lseg(n1, n2, vs);
{
  open lseg(n1, n2, vs);
  if (n1 != n2) {
    lseg_to_lseg(n1->next, n2);
  }
  close lseg(n1, n2, vs);
}

lemma void lseg_to_lseg_append(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, ?vs1) &*& lseg(n2, n3, ?vs2);
  ensures lseg(n1, n3, append(vs1, vs2));
{
  open lseg(n1, n2, vs1);
  if (n1 != n2) {
    lseg_to_lseg_append(n1->next, n2, n3);
  }
  close lseg(n1, n3, append(vs1, vs2));
}

lemma void lseg_to_lseg_nil(struct node *n1, struct node *n2)
  requires lseg(n1, n2, nil);
  ensures n1 == n2;
{
  open lseg(n1, n2, nil);
  if (n1 != n2) {
    lseg_to_lseg_nil(n1->next, n2);
  }
  close lseg(n1, n2, nil);
}
@*/

/*@
fixpoint int length_of_lseg(struct node *n1, struct node *n2) {
  return n1 == n2 ? 0 : 1 + length_of_lseg(n1->next, n2);
}
@*/

/*@
lemma void lseg_length(struct node *n1, struct node *n2)
  requires lseg(n1, n2, ?vs);
  ensures lseg(n1, n2, vs) &*& length_of_lseg(n1, n2) == length(vs);
{
  open lseg(n1, n2, vs);
  if (n1 != n2) {
    lseg_length(n1->next, n2);
  }
  close lseg(n1, n2, vs);
}
@*/

/*@
lemma void lseg_to_lseg_length(struct node *n1, struct node *n2)
  requires lseg(n1, n2, ?vs);
  ensures lseg(n1, n2, vs) &*& length_of_lseg(n1, n2) == length(vs);
{
  lseg_length(n1, n2);
}
@*/

/*@
lemma void lseg_to_lseg_length_append(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, ?vs1) &*& lseg(n2, n3, ?vs2);
  ensures lseg(n1, n3, append(vs1, vs2)) &*& length_of_lseg(n1, n3) == length(vs1) + length(vs2);
{
  lseg_to_lseg_append(n1, n2, n3);
  lseg_to_lseg_length(n1, n3);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil(struct node *n1, struct node *n2)
  requires lseg(n1, n2, nil);
  ensures n1 == n2 &*& length_of_lseg(n1, n2) == 0;
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_length(n1, n2);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, ?vs);
  ensures n1 == n2 &*& lseg(n2, n3, vs) &*& length_of_lseg(n1, n3) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_length(n2, n3);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil(struct node *n1, struct node *n2, struct node *n3)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil);
  ensures n1 == n2 &*& n2 == n3 &*& length_of_lseg(n1, n3) == 0;
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_length(n1, n3);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& lseg(n3, n4, vs) &*& length_of_lseg(n1, n4) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_length(n3, n4);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& lseg(n4, n5, vs) &*& length_of_lseg(n1, n5) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_length(n4, n5);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& lseg(n5, n6, vs) &*& length_of_lseg(n1, n6) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_length(n5, n6);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& lseg(n6, n7, vs) &*& length_of_lseg(n1, n7) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_length(n6, n7);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& lseg(n7, n8, vs) &*& length_of_lseg(n1, n8) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_length(n7, n8);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& lseg(n8, n9, vs) &*& length_of_lseg(n1, n9) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_length(n8, n9);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& lseg(n9, n10, vs) &*& length_of_lseg(n1, n10) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_length(n9, n10);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& lseg(n10, n11, vs) &*& length_of_lseg(n1, n11) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_length(n10, n11);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& lseg(n11, n12, vs) &*& length_of_lseg(n1, n12) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_length(n11, n12);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& lseg(n12, n13, vs) &*& length_of_lseg(n1, n13) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_length(n12, n13);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& lseg(n13, n14, vs) &*& length_of_lseg(n1, n14) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_length(n13, n14);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& lseg(n14, n15, vs) &*& length_of_lseg(n1, n15) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_length(n14, n15);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& lseg(n15, n16, vs) &*& length_of_lseg(n1, n16) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_length(n15, n16);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& lseg(n16, n17, vs) &*& length_of_lseg(n1, n17) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_length(n16, n17);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& lseg(n17, n18, vs) &*& length_of_lseg(n1, n18) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_length(n17, n18);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& lseg(n18, n19, vs) &*& length_of_lseg(n1, n19) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_length(n18, n19);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& lseg(n19, n20, vs) &*& length_of_lseg(n1, n20) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_length(n19, n20);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& n19 == n20 &*& lseg(n20, n21, vs) &*& length_of_lseg(n1, n21) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_nil(n19, n20);
  lseg_to_lseg_length(n20, n21);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21, struct node *n22)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, nil) &*& lseg(n21, n22, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& n19 == n20 &*& n20 == n21 &*& lseg(n21, n22, vs) &*& length_of_lseg(n1, n22) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_nil(n19, n20);
  lseg_to_lseg_nil(n20, n21);
  lseg_to_lseg_length(n21, n22);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21, struct node *n22, struct node *n23)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, nil) &*& lseg(n21, n22, nil) &*& lseg(n22, n23, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& n19 == n20 &*& n20 == n21 &*& n21 == n22 &*& lseg(n22, n23, vs) &*& length_of_lseg(n1, n23) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_nil(n19, n20);
  lseg_to_lseg_nil(n20, n21);
  lseg_to_lseg_nil(n21, n22);
  lseg_to_lseg_length(n22, n23);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21, struct node *n22, struct node *n23, struct node *n24)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, nil) &*& lseg(n21, n22, nil) &*& lseg(n22, n23, nil) &*& lseg(n23, n24, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& n19 == n20 &*& n20 == n21 &*& n21 == n22 &*& n22 == n23 &*& lseg(n23, n24, vs) &*& length_of_lseg(n1, n24) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_nil(n19, n20);
  lseg_to_lseg_nil(n20, n21);
  lseg_to_lseg_nil(n21, n22);
  lseg_to_lseg_nil(n22, n23);
  lseg_to_lseg_length(n23, n24);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21, struct node *n22, struct node *n23, struct node *n24, struct node *n25)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, nil) &*& lseg(n21, n22, nil) &*& lseg(n22, n23, nil) &*& lseg(n23, n24, nil) &*& lseg(n24, n25, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& n19 == n20 &*& n20 == n21 &*& n21 == n22 &*& n22 == n23 &*& n23 == n24 &*& lseg(n24, n25, vs) &*& length_of_lseg(n1, n25) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_nil(n19, n20);
  lseg_to_lseg_nil(n20, n21);
  lseg_to_lseg_nil(n21, n22);
  lseg_to_lseg_nil(n22, n23);
  lseg_to_lseg_nil(n23, n24);
  lseg_to_lseg_length(n24, n25);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21, struct node *n22, struct node *n23, struct node *n24, struct node *n25, struct node *n26)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, nil) &*& lseg(n21, n22, nil) &*& lseg(n22, n23, nil) &*& lseg(n23, n24, nil) &*& lseg(n24, n25, nil) &*& lseg(n25, n26, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& n19 == n20 &*& n20 == n21 &*& n21 == n22 &*& n22 == n23 &*& n23 == n24 &*& n24 == n25 &*& lseg(n25, n26, vs) &*& length_of_lseg(n1, n26) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_nil(n19, n20);
  lseg_to_lseg_nil(n20, n21);
  lseg_to_lseg_nil(n21, n22);
  lseg_to_lseg_nil(n22, n23);
  lseg_to_lseg_nil(n23, n24);
  lseg_to_lseg_nil(n24, n25);
  lseg_to_lseg_length(n25, n26);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21, struct node *n22, struct node *n23, struct node *n24, struct node *n25, struct node *n26, struct node *n27)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, nil) &*& lseg(n21, n22, nil) &*& lseg(n22, n23, nil) &*& lseg(n23, n24, nil) &*& lseg(n24, n25, nil) &*& lseg(n25, n26, nil) &*& lseg(n26, n27, ?vs);
  ensures n1 == n2 &*& n2 == n3 &*& n3 == n4 &*& n4 == n5 &*& n5 == n6 &*& n6 == n7 &*& n7 == n8 &*& n8 == n9 &*& n9 == n10 &*& n10 == n11 &*& n11 == n12 &*& n12 == n13 &*& n13 == n14 &*& n14 == n15 &*& n15 == n16 &*& n16 == n17 &*& n17 == n18 &*& n18 == n19 &*& n19 == n20 &*& n20 == n21 &*& n21 == n22 &*& n22 == n23 &*& n23 == n24 &*& n24 == n25 &*& n25 == n26 &*& lseg(n26, n27, vs) &*& length_of_lseg(n1, n27) == length(vs);
{
  lseg_to_lseg_nil(n1, n2);
  lseg_to_lseg_nil(n2, n3);
  lseg_to_lseg_nil(n3, n4);
  lseg_to_lseg_nil(n4, n5);
  lseg_to_lseg_nil(n5, n6);
  lseg_to_lseg_nil(n6, n7);
  lseg_to_lseg_nil(n7, n8);
  lseg_to_lseg_nil(n8, n9);
  lseg_to_lseg_nil(n9, n10);
  lseg_to_lseg_nil(n10, n11);
  lseg_to_lseg_nil(n11, n12);
  lseg_to_lseg_nil(n12, n13);
  lseg_to_lseg_nil(n13, n14);
  lseg_to_lseg_nil(n14, n15);
  lseg_to_lseg_nil(n15, n16);
  lseg_to_lseg_nil(n16, n17);
  lseg_to_lseg_nil(n17, n18);
  lseg_to_lseg_nil(n18, n19);
  lseg_to_lseg_nil(n19, n20);
  lseg_to_lseg_nil(n20, n21);
  lseg_to_lseg_nil(n21, n22);
  lseg_to_lseg_nil(n22, n23);
  lseg_to_lseg_nil(n23, n24);
  lseg_to_lseg_nil(n24, n25);
  lseg_to_lseg_nil(n25, n26);
  lseg_to_lseg_length(n26, n27);
}
@*/

/*@
lemma void lseg_to_lseg_length_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil_append_nil(struct node *n1, struct node *n2, struct node *n3, struct node *n4, struct node *n5, struct node *n6, struct node *n7, struct node *n8, struct node *n9, struct node *n10, struct node *n11, struct node *n12, struct node *n13, struct node *n14, struct node *n15, struct node *n16, struct node *n17, struct node *n18, struct node *n19, struct node *n20, struct node *n21, struct node *n22, struct node *n23, struct node *n24, struct node *n25, struct node *n26, struct node *n27, struct node *n28)
  requires lseg(n1, n2, nil) &*& lseg(n2, n3, nil) &*& lseg(n3, n4, nil) &*& lseg(n4, n5, nil) &*& lseg(n5, n6, nil) &*& lseg(n6, n7, nil) &*& lseg(n7, n8, nil) &*& lseg(n8, n9, nil) &*& lseg(n9, n10, nil) &*& lseg(n10, n11, nil) &*& lseg(n11, n12, nil) &*& lseg(n12, n13, nil) &*& lseg(n13, n14, nil) &*& lseg(n14, n15, nil) &*& lseg(n15, n16, nil) &*& lseg(n16, n17, nil) &*& lseg(n17, n18, nil) &*& lseg(n18, n19, nil) &*& lseg(n19, n20, nil) &*& lseg(n20, n21, nil) &*& lseg(n21, n22, nil) &*& lseg(n22, n23, nil) &*& lseg(n23, n24, nil) &*& lseg(n24, n25, nil) &*& lseg(n