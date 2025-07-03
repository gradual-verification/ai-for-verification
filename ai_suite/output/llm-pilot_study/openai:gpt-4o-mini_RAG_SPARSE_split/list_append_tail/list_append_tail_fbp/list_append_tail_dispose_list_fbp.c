#include <stdlib.h>

struct node {
    struct node *next;
    int value;
};

struct stack {
    struct node *head;
};

/*@

predicate nodes(struct node *node, int count) =
    node == 0 ? count == 0 : 0 < count &*& node->next |-> ?next &*& node->value |-> ?value &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
    stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

@*/

// TODO: make this function pass the verification
struct stack *create_stack() 
    //@ requires true;
    //@ ensures stack(result, 0);
{
    struct stack *stack = malloc(sizeof(struct stack));
    if (stack == 0) { abort(); }
    stack->head = 0;
    //@ close nodes(0, 0);
    //@ close stack(stack, 0);
    return stack;
}

// TODO: make this function pass the verification
void push(struct stack *stack, int value)
    //@ requires stack(stack, ?count);
    //@ ensures stack(stack, count + 1);
{
    //@ open stack(stack, count);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) { abort(); }
    n->next = stack->head;
    n->value = value;
    stack->head = n;
    //@ close nodes(n, count + 1);
    //@ close stack(stack, count + 1);
}

// TODO: make this function pass the verification
int pop(struct stack *stack)
    //@ requires stack(stack, ?count) &*& 0 < count;
    //@ ensures stack(stack, count - 1);
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ open nodes(head, count);
    int result = head->value;
    stack->head = head->next;
    free(head);
    //@ close stack(stack, count - 1);
    return result;
}

// TODO: make this function pass the verification
void dispose(struct stack *stack) 
    //@ requires stack(stack, ?count);
    //@ ensures true;
{
    //@ open stack(stack, count);
    struct node *current = stack->head;
    while (current != 0) 
        //@ invariant nodes(current, _); 
    {
        //@ open nodes(current, _);
        struct node *oldcurrent = current;
        current = current->next;
        free(oldcurrent);
    }
    //@ open nodes(0, _);
    free(stack);
}

// TODO: make this function pass the verification
int stack_get_count(struct stack *stack)
    //@ requires stack(stack, ?count) &*& count <= INT_MAX;
    //@ ensures stack(stack, count) &*& result == count;
{
    //@ open stack(stack, count);
    struct node *head = stack->head;
    //@ nodes_to_lseg_lemma(head);
    struct node *n = head;
    int i = 0;
    //@ close lseg(head, head, 0);
    while (n != 0)
        //@ invariant lseg(head, n, i) &*& lseg(n, 0, count - i) &*& i <= count &*& count <= INT_MAX;
    {
        //@ open lseg(n, 0, count - i);
        n = n->next;
        i++;
        //@ lseg_add_lemma(head);
    }
    //@ open lseg(0, 0, _);
    //@ lseg_to_nodes_lemma(head);
    //@ close stack(stack, count);
    return i;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct stack *s = create_stack();
    push(s, 1);
    push(s, 2);
    push(s, 3);
    int r1 = pop(s);
    int r2 = pop(s);
    int r3 = pop(s);
    //@ assert r3 == 1;
    dispose(s);
    return 0;
}