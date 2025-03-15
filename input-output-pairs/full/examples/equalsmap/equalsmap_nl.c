#include "stdlib.h"

struct node {
    struct node *next;
    void *key;
    void *value;
};


/**
 * Description:
 * The `map_nil` function returns a null pointer, indicating the end of a mapped list.
 *
 * @returns A null pointer.
 */
struct node *map_nil()
{
    return 0;
}
/**
 * Description:
 * The `map_cons` function creates a new node with the given key and value, and attaches it to the provided tail node.
 *
 * @param key The key to be stored in the new node.
 * @param value The value to be stored in the new node.
 * @param tail The tail node to which the new node will be attached.
 * @returns A pointer to the newly created node.
 */
struct node *map_cons(void *key, void *value, struct node *tail)
{
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    n->key = key;
    n->value = value;
    n->next = tail;
    return n;
}
/**
 * Description:
 * The `map_dispose` function recursively frees of all nodes in the map, starting from the given node.
 *
 * @param map The head node of the map to be disposed of.
 */
void map_dispose(struct node *map)
{

    if (map != 0) {
        map_dispose(map->next);
        free(map);
    }
}


/**
 * Description:
 * The `map_contains_key` function checks if the given key exists in the map by recursively traversing through the map nodes.
 *
 * @param map        The head node of the map to search.
 * @param key        The key to search for.
 * @param equalsFunc A function pointer used to compare keys for equality.
 * @return           True if the key exists in the map, otherwise false.
 */
bool map_contains_key(struct node *map, void *key, equalsFuncType *equalsFunc)
{
   
    if (map == 0)
        return false;
    else {
        
        bool eq = equalsFunc(map->key, key);
        if (eq)
            return true;
        else {
           
            return map_contains_key(map->next, key, equalsFunc);
        }
    }
}

struct foo {
    int value;
};


/**
 * Description:
 * The `foo_equals` function compares two foo structures for equality based on their `value` members.
 *
 * @param f1 Pointer to the first foo structure.
 * @param f2 Pointer to the second foo structure.
 * @return True if the `value` members of the two foo structures are equal, otherwise false.
 */
bool foo_equals(struct foo *f1, struct foo *f2)
{
    
    return f1->value == f2->value;
   
}

/**
 * Description:
 * The `create_foo` function dynamically allocates memory for a foo structure
 * and initializes its `value` member with the provided value.
 *
 * @param value The value to be assigned to the `value` member of the created foo structure.
 * @return Pointer to the newly created foo structure.
 */
struct foo *create_foo(int value);
{
    struct foo *foo = malloc(sizeof(struct foo));
    if (foo == 0) abort();
    foo->value = value;
    return foo;
}

/**
 * Description:
 * The `main` function checks whether the created map has and doesn't an element 
 * whose value equal to the value of the created one.
 */
int main()
{
    struct foo *foo1 = create_foo(100);
    struct foo *foo2 = create_foo(200);
    struct foo *foo3 = create_foo(300);
    struct node *map = map_nil();
    map = map_cons(foo3, 0, map);
    map = map_cons(foo2, 0, map);
    map = map_cons(foo1, 0, map);
    struct foo *fooX = create_foo(200);
    struct foo *fooY = create_foo(400);
 
    bool c = map_contains_key(map, fooX, foo_equals);
    assert(c);
   
    c = map_contains_key(map, fooY, foo_equals);
    assert(!c);

    free(foo1);
    free(foo2);
    free(foo3);
    free(fooX);
    free(fooY);
    map_dispose(map);
    return 0;
}
