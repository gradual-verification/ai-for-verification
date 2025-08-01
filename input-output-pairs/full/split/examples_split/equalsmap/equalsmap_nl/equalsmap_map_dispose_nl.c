#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};

struct foo {
    int value;
};


// TODO: make this function pass the verification
/**
 * Description:
 * The `map_dispose` function frees of all nodes in the map.
 *
 * @param map The head node of the map to be disposed of
 * 
 * This function makes sure that all nodes in the map are freed.
 */
void map_dispose(struct node *map)
{

    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}

