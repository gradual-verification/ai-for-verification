#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate student(struct student *s;) =
    s->name[..100] |-> ?cs &*& s->age |-> _;

predicate students(struct student *students, int count;) =
    count == 0 ?
        emp
    :
        student(students) &*&
        students(students + 1, count - 1);
@*/

struct student *read_students(int *count)
//@ requires *count |-> _;
//@ ensures *count |-> ?nb &*& students(result, nb);
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
    /*@ invariant
        0 <= i <= *count &*&
        students(result, i) &*&
        *count |-> ?nb;
    @*/
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ open students(result, i);
        //@ close student(&result[i]);
        //@ close students(result, i + 1);
    }
    //@ leak students(result, *count);
    return result;
}

struct point {
    int x;
    int y;
};

int main() 
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    //@ leak malloc_block(points);
    free((void *)points); 
    return 0;
}
