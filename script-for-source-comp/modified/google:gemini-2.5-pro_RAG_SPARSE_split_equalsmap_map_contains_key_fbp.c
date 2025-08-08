
struct node {
    struct node *next;
    void *key;
    void *value;
};



struct foo {
    int value;
};



typedef bool equalsFuncType/*@ (list<void *> keys, void *key00, list<void *> eqKeys, predicate() p) @*/(void *key, void *key0);



bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
{
    open map(map, entries);
    if (map == 0) {
        close map(0, nil);
        return false;
    } else {
        bool eq = equalsFunc(map->key, key);
        if (eq) {
            close map(map, entries);
            return true;
        } else {
            bool rec_result = map_contains_key(map->next, key, equalsFunc);
            close map(map, entries);
            return rec_result;
        }
    }
}
