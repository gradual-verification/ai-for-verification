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

// Predicate for a single, initialized student struct.
// It holds that the 'name' field contains a valid C string and 'age' is an integer.
predicate student_cell(struct student *s) =
    chars(s->name, 100, ?cs) &*& mem('\0', cs) == true &*&
    integer(&s->age, _);

// Predicate for an array of initialized student structs.
predicate students(struct student *arr, int count) =
    count == 0 ?
        emp
    :
        student_cell(arr) &*& students(arr + 1, count - 1);

// A lemma to prove that two adjacent 'students' blocks can be merged.
// This is useful for inductive reasoning over arrays, especially in loops.
lemma_auto void students_join(struct student *arr)
    requires students(arr, ?n) &*& students(arr + n, ?m);
    ensures students(arr, n + m);
{
    open students(arr, n);
    if (n > 0) {
        students_join(arr + 1);
    }
}

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
    //@ requires integer(count, _);
    //@ ensures integer(count, ?n) &*& 0 <= n &*& students(result, n) &*& malloc_block_struct_student(result, n);
{
    printf("How many students?\n");
    //@ open integer(count, _);
    scanf(" %d", count);
    //@ assert integer(count, ?n_read);
    
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    
    int n = *count;
    //@ assume(0 <= n);
    
    struct student *result = malloc((size_t)n * sizeof(struct student));
    if (result == 0) abort();
    
    //@ div_rem((size_t)n * sizeof(struct student), sizeof(struct student));
    //@ close students(result, 0);
    
    for (int i = 0; i < n; i++)
        /*@
        invariant 0 <= i &*& i <= n &*&
                  integer(count, n) &*&
                  students(result, i) &*&
                  chars_((char *)(result + i), (size_t)(n - i) * sizeof(struct student), _) &*&
                  malloc_block_struct_student(result, n);
        @*/
    {
        //@ chars__split((char *)(result + i), sizeof(struct student));
        //@ chars__split((char *)(result + i), 100);
        //@ chars__to_int_(&result[i].age);
        
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
        
        // After the two scanf calls, we have the necessary chunks to form a `student_cell`.
        // Specifically: `chars(result[i].name, 100, ?cs) &*& mem('\0', cs) == true`
        // and `integer(&result[i].age, _)`.
        
        //@ close student_cell(result + i);
        //@ students_join(result);
    }
    
    //@ chars__inv(); // Consume the empty chars_ chunk at the end of the loop.
    return result;
}