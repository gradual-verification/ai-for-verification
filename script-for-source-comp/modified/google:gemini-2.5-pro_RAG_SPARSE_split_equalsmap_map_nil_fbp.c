predicate map(struct node *n; list<pair<void *, void *> > entries) =
    n == 0 ?
        entries == nil
    :
        ...

struct node {
    struct node *next;
    void *key;
    void *value;
};



struct foo {
    int value;
};


struct node *map_nil()
{
    return 0;
}
