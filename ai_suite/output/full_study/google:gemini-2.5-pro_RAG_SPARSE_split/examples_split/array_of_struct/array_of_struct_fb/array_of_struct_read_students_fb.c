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
        students(students + 1, count - 1);

predicate malloc_block_student(struct student *p; int count) =
    malloc_block(p, ?size) &*& [_]divrem(size, sizeof(struct student), count, 0);

lemma void students_snoc(struct student *s, int i)
    requires i >= 0 &*& students(s, i) &*&
             s[i].name[..100] |-> ?cs &*& mem('\0', cs) == true &*& s[i].age |-> _;
    ensures students(s, i + 1);
{
    if (i == 0) {
        close students(s + 1, 0);
        close students(s, 1);
    } else {
        open students(s, i);
        students_snoc(s + 1, i - 1);
        close students(s, i + 1);
    }
}
@*/


// TODO: make this function pass the verification
struct student *read_students(int *count)
//@ requires *count |-> _;
//@ ensures *count |-> ?nb &*& students(result, nb) &*& malloc_block_student(result, nb);
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    int nb = *count;
    struct student *result = malloc(nb * sizeof(struct student));
    if (result == 0) abort();
    
    //@ divrem_intro(nb * sizeof(struct student), sizeof(struct student), nb, 0);
    //@ close malloc_block_student(result, nb);
    
    //@ close students(result, 0);
    for (int i = 0; i < nb; i++)
        /*@
        invariant 0 <= i &*& i <= nb &*& *count |-> nb &*&
                  students(result, i) &*&
                  chars_((void *)(result + i), (nb - i) * sizeof(struct student), _) &*&
                  malloc_block_student(result, nb);
        @*/
    {
        //@ chars_split((void *)(result + i), sizeof(struct student));
        
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        
        //@ students_snoc(result, i);
    }
    
    //@ open chars_((void *)(result + nb), 0, _);
    return result;
}