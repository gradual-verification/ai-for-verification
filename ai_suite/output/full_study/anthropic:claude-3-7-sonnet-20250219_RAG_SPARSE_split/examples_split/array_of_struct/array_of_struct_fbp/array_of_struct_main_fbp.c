#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

struct point {
    int x;
    int y;
};

/*@
predicate students(struct student *students, int count;) =
    count == 0 ?
        true
    :
        students->name[..100] |-> ?cs &*& mem('\0', cs) == true &*& students->age |-> _ &*&
        struct_student_padding(students) &*&
        students(students + 1, count - 1);
@*/

/*@
predicate points(struct point *points, int count;) =
    count == 0 ?
        true
    :
        points->x |-> _ &*& points->y |-> _ &*&
        struct_point_padding(points) &*&
        points(points + 1, count - 1);
@*/

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    //@ open malloc_block(points, 2 * sizeof(struct point));
    if (points == 0) abort();
    
    //@ close points(points, 0);
    //@ close points(points + 1, 0);
    //@ close points(points, 1);
    //@ close points(points, 2);
    
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    
    //@ open points(points, 2);
    //@ open points(points + 1, 1);
    //@ open points(points + 1, 0);
    //@ open points(points, 0);
    
    free((void *)points); 
    return 0;
}