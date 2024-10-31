#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate students(struct student *arr, int n) = 
    structs(struct student)(arr, n);
@*/

struct student *read_students(int *count)
    //@ requires *count |-> _;
    //@ ensures *count |-> ?nb &*& nb >= 0 &*& students(result, nb);
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ malloc_block(result, *count * sizeof(struct student));
    //@ close structs(struct student)(result, *count);
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i &*& i <= *count &*& structs(struct student)(result, *count);
    {
        //@ structs_split(struct student)(result, i, 1 + (*count - (i + 1)));
        //@ structs_split(struct student)(result + i, 1, *count - (i + 1));
        //@ open structs(struct student)(result + i, 1);
        //@ open struct_student(result + i);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close struct_student(result + i);
        //@ close structs(struct student)(result + i, 1);
        //@ structs_join(struct student)(result + i, 1, *count - (i + 1));
        //@ structs_join(struct student)(result, i, 1 + (*count - (i + 1)));
    }
    return result;
}

struct point {
    int x;
    int y;
};

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ malloc_block(points, 2 * sizeof(struct point));
    //@ close structs(struct point)(points, 2);
    //@ open structs(struct point)(points, 2);
    //@ open struct_point(points);
    points[0].x = 10;
    points[0].y = 20;
    //@ close struct_point(points);
    //@ open struct_point(points + 1);
    points[1].x = 30;
    points[1].y = 40;
    //@ close struct_point(points + 1);
    //@ close structs(struct point)(points, 2);
    //@ open structs(struct point)(points, 2);
    free(points); 
    return 0;
}
