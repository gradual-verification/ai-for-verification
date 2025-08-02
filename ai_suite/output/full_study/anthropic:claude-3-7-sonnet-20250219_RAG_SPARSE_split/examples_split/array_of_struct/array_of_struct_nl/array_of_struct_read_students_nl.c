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
// Predicate to represent a properly initialized student
predicate student_initialized(struct student *s) =
    s->name |-> ?name_chars &*& 
    s->age |-> ?age &*&
    chars(name_chars, 100, _);

// Predicate to represent an array of initialized students
predicate students_array(struct student *array, int count) =
    count <= 0 ?
        emp
    :
        student_initialized(array) &*&
        students_array(array + 1, count - 1);
@*/

// TODO: make this function pass the verification
/***
 * Description:
The read_students function reads student information from user input and allocates memory for storing the students' data.

@param count A pointer to an integer that will store the number of students entered by the user.

The function makes sure that the return value is a pointer to an array of students, 
whose number is stored in count and they are initialized with name and age. 
*/
struct student *read_students(int *count)
    //@ requires count != NULL &*& integer(count, _);
    /*@ ensures result == 0 ?
                integer(count, ?c) &*& c <= 0
            :
                integer(count, ?c) &*& c > 0 &*&
                malloc_block(result, c * sizeof(struct student)) &*&
                students_array(result, c);
    @*/
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ assert integer(count, ?num_students);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    
    /*@
    if (*count > 0) {
        int i = 0;
        for (i = 0; i < *count; i++)
            invariant 0 <= i &*& i <= *count &*&
                     integer(count, *count) &*&
                     malloc_block(result, *count * sizeof(struct student)) &*&
                     students_array(result, i);
        {
            //@ close student_initialized(&result[i]);
        }
    }
    @*/
    
    for (int i = 0; i < *count; i++)
        /*@ invariant 0 <= i &*& i <= *count &*&
                     integer(count, *count) &*&
                     malloc_block(result, *count * sizeof(struct student)) &*&
                     students_array(result, i);
        @*/
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close student_initialized(&result[i]);
    }
    
    return result;
}