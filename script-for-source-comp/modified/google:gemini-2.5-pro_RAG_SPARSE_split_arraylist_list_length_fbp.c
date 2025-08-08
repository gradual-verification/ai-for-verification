
struct arraylist {
    void ** data;
    int size;
    int capacity;
};



int list_length(struct arraylist * a)
{
    return a->size;
}
