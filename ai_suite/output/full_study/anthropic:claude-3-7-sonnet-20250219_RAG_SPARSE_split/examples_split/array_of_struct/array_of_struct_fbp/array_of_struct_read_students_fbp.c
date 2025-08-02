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


// TODO: make this function pass the verification
struct student *read_students(int *count)
//@ requires *count |-> _;
//@ ensures *count |-> ?nb &*& students(result, nb) &*& malloc_block_chars((void *)result, nb * sizeof(struct student));
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ assert *count |-> ?nb;
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    
    //@ assert malloc_block_chars((void *)result, nb * sizeof(struct student));
    
    for (int i = 0; i < *count; i++)
    //@ invariant 0 <= i &*& i <= nb &*& *count |-> nb &*& malloc_block_chars((void *)result, nb * sizeof(struct student)) &*& students(result, i);
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        
        //@ close students(result + i + 1, 0);
        //@ close students(result + i, 1);
    }
    
    return result;
}