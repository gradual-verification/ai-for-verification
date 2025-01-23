
/***
 * Description: 
The sum_of_range function calculates the sum of all integers in the range from 0 to n-1.

@param `n` - the upper limit of the range (exclusive).

It requires: The parameter `n` must be a non-negative integer.
It ensures: The result is equal to the sum of all integers in the range from 0 to n-1.
*/
int sum_of_range(int n)
{
    int count = 0;
    int sum = 0;
    while (count != n)
    {
        sum = sum + count;
        count = count + 1;
    }
    return sum;
}

int main()
{
    return 0;
}