
struct node {
    struct node *next;
    int value;
};



void dispose_nodes(struct node *head)
{
    if (head == 0) return;
    struct node *next = head->next;
    free(head);
    dispose_nodes(next);
}
