
struct node {
    struct node *next;
    void *key;
    void *value;
};



struct foo {
    int value;
};


bool foo_equals(struct foo *f1, struct foo *f2)
{
    bool result = f1->value == f2->value;
    return result;
}
