#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate struct_student(struct student* s) =
    chars(s->name, 100, ?cs) &*&
    mem('\0', cs) == true &*&
    s->age |-> _ &*&
    struct_student_padding(s);

predicate students(struct student *students, int count) =
    count == 0 ?
        emp
    :
        struct_student(students) &*&
        students(students + 1, count - 1);
@*/

struct student *read_students(int *count)
    //@ requires *count |-> _;
    //@ ensures *count |-> ?nb &*& students(result, nb) &*& malloc_block_chars((void *)result, nb * sizeof(struct student));
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ assume(result != 0);
    //@ chars((void *)result, *count * sizeof(struct student), _);
    //@ close students(result, 0);
    for (int i = 0; i < *count; i++)
    /*@
        invariant
            0 <= i &*& i <= *count &*&
            chars((void *)(result + i), (*count - i) * sizeof(struct student), _) &*&
            students(result, i) &*&
            malloc_block_chars((void*)result, *count * sizeof(struct student));
    @*/
    {
        //@ chars_split((void *)(result + i), sizeof(struct student));
        //@ open chars((void *)(&result[i]), sizeof(struct student), _);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close struct_student(&result[i]);
        //@ close students(result, i + 1);
    }
    //@ close students(result, *count);
    return result;
}

struct point {
    int x;
    int y;
};

/*@
predicate struct_point(struct point *p) =
    p->x |-> _ &*& p->y |-> _ &*& struct_point_padding(p);
@*/

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ assume(points != 0);
    //@ chars((void *)points, 2 * sizeof(struct point), _);
    //@ chars_split((void *)points, sizeof(struct point));
    //@ chars_split((void *)(points + 1), sizeof(struct point));

    //@ open chars((void *)(&points[0]), sizeof(struct point), _);
    //@ close struct_point(&points[0]);

    //@ open chars((void *)(&points[1]), sizeof(struct point), _);
    //@ close struct_point(&points[1]);

    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;

    //@ open struct_point(&points[0]);
    //@ open struct_point(&points[1]);
    //@ chars_join((void *)(&points[1]), sizeof(struct point));
    //@ chars_join((void *)points, 2 * sizeof(struct point));

    free((void *)points); 
    return 0;
}
