
struct node {
    struct node *next;
    void *key;
    void *value;
};



struct foo {
    int value;
};



typedef bool equalsFuncType(void *key, void *key0);

bool pointer_equals(void *key, void *key0) //@ : equalsFuncType
{
    return key == key0;
}
