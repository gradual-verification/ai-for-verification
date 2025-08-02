#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

//@ #include "prelude.h"

struct student {
    char name[100];
    int age;
};

//@ predicate student(struct student *s; list<char> name, int age) =
//@     chars(s->name, 100, name) &*& length(name) < 100 &*& integer(&s->age, age);

struct point {
    int x;
    int y;
};

// TODO: make this function pass the verification
/***
 * Description:
The read_students function reads student information from user input and allocates memory for storing the students' data.

@param count A pointer to an integer that will store the number of students entered by the user.

The function makes sure that the return value is a pointer to an array of students, 
whose number is stored in count and they are initialized with name and age. 
*/
//@ requires integer(count, _);
//@ ensures result == 0 ? true : malloc_block(result, *count * sizeof(struct student)) &*& students(result, *count, _);
struct student *read_students(int *count)
    //@ requires integer(count, _);
    //@ ensures result == 0 ? true : malloc_block(result, *count * sizeof(struct student)) &*& students(result, *count, _);
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
        //@ invariant 0 <= i &*& i <= *count &*& malloc_block(result, *count * sizeof(struct student)) &*& students(result, i, _);
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        //@ close student(&result[i], ?name, result[i].age);
    }
    //@ close students(result, *count, _);
    return result;
}

//@ predicate students(struct student *array, int count, list<struct student> students) =
//@     count == 0 ? students == nil : student(&array[0], ?name, ?age) &*& students(array + 1, count - 1, ?students0) &*& students == cons(student(name, age), students0);