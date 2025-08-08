
struct arraylist {
    void ** data;
    int size;
    int capacity;
};


void list_dispose(struct arraylist * a)
{
    void ** data = a -> data;
    int size = a -> size;
    int capacity = a -> capacity;
    free(data);
    free(a);
}
