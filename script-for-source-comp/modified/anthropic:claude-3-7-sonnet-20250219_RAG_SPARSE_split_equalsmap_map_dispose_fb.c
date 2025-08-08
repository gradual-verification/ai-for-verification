
struct node {
    struct node *next;
    void *key;
    void *value;
};



struct foo {
    int value;
};



void map_dispose(struct node *map)
{
    if (map != 0) {
        struct node *next = map->next;
        map_dispose(next);
        free(map);
    }
}
