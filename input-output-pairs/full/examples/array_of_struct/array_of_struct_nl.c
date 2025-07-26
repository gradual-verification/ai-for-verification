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

/***
 * Description:
The read_students function reads student information from user input and allocates memory for storing the students' data.

@param count A pointer to an integer that will store the number of students entered by the user.

The function makes sure that the return value is a pointer to an array of students, 
whose number is stored in count and they are initialized with name and age. 
*/
struct student *read_students(int *count)
{
    printf("How many students?\n");
    scanf(" %d", count);
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
    {
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
    }
    return result;
}

/***
 * Description:
The main function demonstrates safe memory allocation, initialization, and deallocation for an array of structures in C.
*/
int main()
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