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
lemma void students_append(struct student *s, int i, int j)
    requires students(s, i) &*& students(s + i, j);
    ensures students(s, i + j);
{
    open students(s, i);
    if (i > 0) {
        students_append(s + 1, i - 1, j);
        close students(s, i + j);
    }
}
@*/


// TODO: make this function pass the verification
struct student *read_students(int *count)
//@ requires *count |-> _;
//@ ensures *count |-> ?nb &*& students(result, nb) &*& malloc_block_chars((void *)result, nb * sizeof(struct student));
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
        /*@
        invariant
            0 <= i &*& i <= *count &*&
            *count |-> ?nb &*& nb == *count &*&
            students(result, i) &*&
            chars_((void *)(result + i), (nb - i) * sizeof(struct student), _) &*&
            malloc_block(result, nb * sizeof(struct student));
        @*/
    {
        //@ chars_split((char *)(result + i), sizeof(struct student));
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close students(result + i, 1);
        //@ students_append(result, i, 1);
    }
    return result;
}