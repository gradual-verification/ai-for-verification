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
@*/


// TODO: make this function pass the verification
struct student *read_students(int *count)
//@ requires *count |-> _;
//@ ensures *count |-> ?nb &*& students(result, nb);
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ assert *count |-> ?nb;
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    
    //@ assert *count |-> nb;
    //@ assert result != 0;
    
    for (int i = 0; i < *count; i++)
        //@ requires i >= 0 &*& i < nb &*& result + i |-> _ &*& result[i..nb] |-> _;
        //@ ensures result[old_i..nb] |-> _ &*& students(result + old_i, nb - old_i);
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        
        //@ assert result[i].name[..100] |-> ?name_chars;
        //@ assert mem('\0', name_chars) == true;
        //@ assert result[i].age |-> ?age;
        
        //@ close students(result + i + 1, nb - i - 1);
        //@ close students(result + i, nb - i);
    }
    
    //@ assert students(result, nb);
    return result;
}