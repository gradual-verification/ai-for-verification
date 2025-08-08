
struct node {
    struct node *next;
};


struct node *create_list()
{
    return 0;
}

struct node *append_tail(struct node *head)
{
    struct node *new_node = malloc(sizeof(struct node));
    if (new_node == 0) abort();
    new_node->next = 0;

    if (head == 0) {
        return new_node;
    } else {
        struct node *curr = head;
        
        if (curr->next == 0) {
            curr->next = new_node;
            return head;
        } else {
            struct node *tmp = curr;
            curr = curr->next;
            
            
            while (curr->next != 0)
            {
                tmp = curr;
                curr = curr->next;
            }
            curr->next = new_node;
            return head;
        }
    }
}

void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    } else {
    }
}

int main()
{
    struct node *list = create_list();
    
    list = append_tail(list);
    
    list = append_tail(list);
    
    list = append_tail(list);

    dispose_list(list);
    return 0;
}

struct node {
    struct node *next;
};


struct node *create_list()
{
    return 0;
}

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
            struct node *tmp = curr;
            curr = curr->next;
        }
        curr->next = new_node;
        return head;
    }
}

void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    } else {
    }
}

int main()
{
    struct node *list = create_list();
    list = append_tail(list);
    list = append_tail(list);
    list = append_tail(list);

    dispose_list(list);
    return 0;
}

struct node {
    struct node *next;
};


struct node *create_list()
{
    return 0;
}

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
            struct node *tmp = curr;
            curr = curr->next;
        }
        curr->next = new_node;
        return head;
    }
}

void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    } else {
    }
}

int main()
{
    struct node *list = create_list();
    list = append_tail(list);
    list = append_tail(list);
    list = append_tail(list);

    dispose_list(list);
    return 0;
}

struct node {
    struct node *next;
};


struct node *create_list()
{
    return 0;
}

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
            curr = curr->next;
        }
        
        curr->next = new_node;
        return head;
    }
}

void dispose_list(struct node *head)
{
    if (head != 0) {
        dispose_list(head->next);
        free(head);
    } else {
    }
}

int main()
{
    struct node *list = create_list();
    list = append_tail(list);
    list = append_tail(list);
    list = append_tail(list);

    dispose_list(list);
    return 0;
}
