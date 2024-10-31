#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

/*@
predicate student(struct student *s;) =
    chars(s->name, 100, _) &*& s->age |-> _;

predicate students(struct student *array, int count;) =
    count == 0 ? emp :
    student(&array[0]) &*& students(array + 1, count - 1);
@*/

struct student {
    char name[100];
    int age;
};

/*@
requires *count |-> _;
ensures *count |-> ?nb &*& students(result, nb);
@*/
struct student *read_students(int *count)
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students(result, 0);
    for (int i = 0; i < *count; i++)
    /*@
    invariant 0 <= i &*& i <= *count &*& students(result, i);
    @*/
    {
        printf("Please enter the name of student %d:\n", i);
        //@ chars(result[i].name, 100, _);
        if (scanf(" %99s", result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        //@ s->age |-> _;
        scanf(" %d", &result[i].age);
        //@ close student(&result[i]);
        //@ close students(result, i + 1);
    }
    return result;
}

// Specifications for scanf and printf
/*@
requires *p |-> _;
ensures *p |-> _ &*& result == 1;
@*/
int scanf(const char *format, int *p);

/*@
requires chars(buf, n, _);
ensures chars(buf, n, _) &*& result == 1;
@*/
int scanf(const char *format, char *buf);

/*@
requires true;
ensures true;
@*/
int printf(const char *format, ...);

struct point {
    int x;
    int y;
};

/*@
requires true;
ensures true;
@*/
int main()
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ close malloc_block(points, 2 * sizeof(struct point));
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    //@ open malloc_block(points, 2 * sizeof(struct point));
    free((void *)points);
    return 0;
}
