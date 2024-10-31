struct node *nodes_filter(struct node *n, int_predicate *p)
//@ requires nodes(n, ?count) &*& is_int_predicate(p) == true;
//@ ensures nodes(result, ?newCount) &*& newCount <= count;
{
    if (n == 0)
    {
        return 0;
    }
    else
    {
        bool keep = p(n->value);
        if (keep)
        {
            struct node *next = nodes_filter(n->next, p);
            n->next = next;
            return n;
        }
        else
        {
            struct node *next = n->next;
            free(n);
            struct node *result = nodes_filter(next, p);
            return result;
        }
    }
}

void stack_filter(struct stack *stack, int_predicate *p)
//@ requires stack(stack, ?count) &*& is_int_predicate(p) == true;
//@ ensures stack(stack, ?newCount) &*& newCount <= count;
{
    struct node *head = nodes_filter(stack->head, p);
    stack->head = head;
}
