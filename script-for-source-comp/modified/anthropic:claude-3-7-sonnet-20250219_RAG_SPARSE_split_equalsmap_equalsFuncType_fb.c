
struct node {
    struct node *next;
    void *key;
    void *value;
};



struct foo {
    int value;
};



typedef bool equalsFuncType/*@ (list<void *> keys, void *key00, list<void *> eqKeys, predicate() p) @*/(void *key, void *key0);

bool equals(void *key, void *key0)//@ : equalsFuncType
{
    return key == key0;
}
