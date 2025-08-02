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

//@ predicate points(struct point *points, int count;) = count == 0 ? true : point(points, _) &*& points(points + 1, count - 1);

//@ predicate point(struct point *p;) = p->x |-> _ &*& p->y |-> _ &*& struct_point_padding(p);

// TODO: make this function pass the verification
int main() //@ : main
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ close points(points, 2);
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    //@ open points(points, 2);
    //@ open point(points);
    //@ open point(points + 1);
    free((void *)points); 
    return 0;
}