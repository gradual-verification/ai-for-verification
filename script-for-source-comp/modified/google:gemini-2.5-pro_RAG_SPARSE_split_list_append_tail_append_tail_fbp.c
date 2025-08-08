
struct node {
    struct node *next;
};


struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        return new_node;
    } else {
        struct node *curr = head;
        while (curr->next != 0)
        {
            lseg_append(head);
            struct node *tmp = curr;
            curr = curr->next;
        }
        
        curr->next = new_node;
        
        lseg_chain(head, curr, 0);
        
        return head;
    }
}
