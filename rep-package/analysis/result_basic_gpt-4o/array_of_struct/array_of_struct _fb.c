#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@
predicate students(struct student *students, int count;) =
    count == 0 ?
        emp
    :
        (students + count - 1)->name[..100] |-> ?cs &*& (students + count - 1)->age |-> _ &*&
        struct_student_padding(students + count - 1) &*&
        students(students, count - 1);
@*/

struct student *read_students(int *count)
//@ requires *count |-> _;
//@ ensures *count |-> ?nb &*& malloc_block_chars((void *)result, nb * sizeof(struct student)) &*& students(result, nb);
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ integer_limits(count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    // @ mul_mono_l(0, *count, sizeof(struct student));
    //@ div_rem_nonneg(SIZE_MAX, sizeof(struct student));
    //@ mul_mono_l(*count, SIZE_MAX / sizeof(struct student), sizeof(struct student));
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    //@ close students(result, 0);
    //@ assert *count |-> ?nb;
    for (int i = 0; i < *count; i++)
    /*@
    invariant *count |-> nb &*& 0 <= i &*& i <= nb &*& students(result, i) &*& chars_((void *)(result + i), (nb - i) * sizeof(struct student), _);
    @*/
    {
        //@ mul_mono_l(1, nb - i, sizeof(struct student));
        //@ chars__split((void *)(result + i), sizeof(struct student));
        //@ close_struct(result + i);
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

int main() 
//@ requires true;
//@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    //@ div_rem_nonneg(SIZE_MAX, 2);
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ close_struct(points);
    //@ close_struct(points + 1);
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    //@ open_struct(points);
    //@ open_struct(points + 1);
    free((void *)points); 
    return 0;
}
