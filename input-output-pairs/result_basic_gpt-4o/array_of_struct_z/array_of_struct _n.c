#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate student_array(struct student *arr, integer count) =
    malloc_block_student(arr, count) &*&
    count >= 0 &*&
    arr == 0 ? true : (arr->name |-> ?name &*& arr->age |-> ?age &*& chars(name, 100, ?cs) &*& cs[99] == 0) &*&
    count == 0 ? emp : student_array(arr + 1, count - 1);
@*/

/*@
requires count != 0 &*& *count |-> _;
ensures result == 0 ? *count |-> _ : student_array(result, *count);
@*/
struct student *read_students(int *count)
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    /*@ 
    for (int i = 0; i < *count; i++)
        invariant 0 <= i &*& i <= *count &*& student_array(result, i) &*& 
                  (i < *count ? chars(result[i].name, 100, _) : true);
    @*/
    for (int i = 0; i < *count; i++)
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
    }
    return result;
}

struct point {
    int x;
    int y;
};

/*@
predicate point_struct(struct point *p) =
    p->x |-> _ &*& p->y |-> _;
@*/

/*@
requires true;
ensures true;
@*/
int main()
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    /*@ 
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40; 
    @*/
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    free(points);
    return 0;
}