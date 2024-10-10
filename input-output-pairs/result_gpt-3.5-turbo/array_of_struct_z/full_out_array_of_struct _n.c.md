```c CODE and SPEC
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/***
 * Description:
The read_students function reads student information from user input and allocates memory for storing the students' data. 

@param count A pointer to an integer that will store the number of students entered by the user.

The function prompts the user to enter the number of students and stores this value in count. 
It ensures that the number of students is non-negative and that the required memory allocation does not exceed system limits. 
If these checks fail, the program aborts. The function then allocates memory for the array of struct student and,
if allocation fails, the program aborts. For each student, 
it prompts the user to enter the student's name and age, storing this information in the allocated array. 
Finally, the function returns a pointer to the array of students.
*/
struct student *read_students(int *count) 
//@ ensures \result != \null;
{
    //@ assert \valid(count);
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
    }
    return result;
}

struct point {
    int x;
    int y;
};

/***
 * Description:
The main function serves as the entry point of the program, demonstrating safe memory allocation, initialization, and deallocation for an array of structures in C.
 
It performs the following steps:
1. Validates that getting the total size of two instances of struct point will not cause an integer overflow. If an overflow is detected, the program terminates.
2. Allocates memory for two struct point structures. If the memory allocation fails, the program terminates.
3. Initializes the x and y members of the two struct point structures with specific values.
4. Frees the allocated memory to prevent memory leaks.
5. Returns 0 to indicate successful program termination.
*/
int main() 
//@ ensures \result == 0;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    free((void *)points); 
    return 0;
}
```
