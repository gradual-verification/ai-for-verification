#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

// VeriFast headers
#include "verifast.h"

struct student {
    char name[100];
    int age;
};

/*@
predicate malloc_block_student(struct student *p, int count) =
  malloc_block(p, count * sizeof(struct student));

predicate student_array(struct student *arr, int count;) =
  count == 0 ? emp : 
    struct_student_name(&arr[0], ?name) &*&
    struct_student_age(&arr[0], ?age) &*&
    student_array(arr + 1, count - 1);
@*/

/*@
  requires  pointer(count, _) &*& *count |-> _;
  ensures   pointer(count, _) &*& *count |-> ?c &*& c >= 0 &*&
            result == 0 ? emp : 
            malloc_block_student(result, c) &*& student_array(result, c);
@*/
struct student *read_students(int *count)
{
    printf("How many students?\n");
    //@ open pointer(count, _);
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
  
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    
    //@ close student_array(result, *count);
    for (int i = 0; i < *count; i++)
    //@ invariant 0 <= i <= *count &*& student_array(result, *count);
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
predicate point_array(struct point *arr, int count;) =
  count == 0 ? emp : 
    struct_point_x(&arr[0], ?x) &*&
    struct_point_y(&arr[0], ?y) &*&
    point_array(arr + 1, count - 1);
@*/

/*@
  requires true;
  ensures  result == 0 ? emp : malloc_block_point(result, 2) &*& point_array(result, 2);
@*/
int main()
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    
    //@ close point_array(points, 2);
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    //@ open point_array(points, 2);
    free((void *)points);
    return 0;
}
