#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "verifast.h"

struct student {
    char name[100];
    int age;
};

// Predicate to represent a struct student in memory
/*@
predicate student(int index, struct student *s;) =
    s != 0 &*&
    s->name |-> ?name_string &*&
    s->age |-> ?age &*& 
    chars(name_string, 100, ?cs);
@*/

/*@
 requires count != 0 &*& *count |-> _;
  // Precondition: count is a valid pointer
 ensures result == 0 ? true : (*count |-> ?n_students &*& 
    n_students >= 0 &*&
    malloc_block_student_array(result, n_students) &*&
    forall_p(int i; 0 <= i && i < n_students; student(i, result + i)));
  // Postcondition: Either result is null, or memory for n_students students is allocated
 */
struct student *read_students(int *count)
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
    /*@
    invariant 0 <= i && i <= *count &*&
        malloc_block_student_array(result, *count) &*&
        forall_p(int j; 0 <= j && j < i; student(j, result + j));
      */
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close student(i, result + i);
    }
    return result;
}

struct point {
    int x;
    int y;
};

/*@
 requires true;
  // Precondition: None
 ensures result == 0 ? true : malloc_block_point_array(result, 2) &*&
    result != 0 &*&
    result[0].x |-> 10 &*&
    result[0].y |-> 20 &*&
    result[1].x |-> 30 &*&
    result[1].y |-> 40;
  // Postcondition: Either result is null, or valid memory is allocated and initialized for two points
 */
int main()
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    //@ close malloc_block_point_array(points, 2);
    free((void *)points); 
    return 0;
}
