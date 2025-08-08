


int read_int()
{
    int x;
    scanf("%i", &x);
    return x;
}


void merge_sort_core(int *pxs, int *pys, int n)
{
    if (n >= 2) {
        int *left = pxs;
        int nleft = n / 2;
        int *right = pxs + nleft;
        int nright = n - n / 2;
        
        merge_sort_core(left, pys, nleft);
        merge_sort_core(right, pys, nright);
        
        
        int i = 0;
        int j = 0;
        int k = 0;
        for (;;)
        {
            if (i == nleft) {
                if (j == nright) {
                    break;
                } else {
                    pys[k] = right[j];
                    j++;
                    k++;
                }
            } else {
                if (j == nright) {
                    pys[k] = left[i];
                    i++;
                    k++;
                } else {
                    if (left[i] <= right[j]) {
                        pys[k] = left[i];
                        i++;
                        k++;
                    } else {
                        pys[k] = right[j];
                        j++;
                        k++;
                    }
                }
            }
        }
        
        
        for (int p = 0; ; p++)
        {
            if (p >= n) break;
            pxs[p] = pys[p];
            p++;
        }
    }
}


void merge_sort(int *pxs, int n)
{
    if (n <= 0) return;
    int *pys = malloc(n * sizeof(int));
    if (pys == 0) abort();
    merge_sort_core(pxs, pys, n);
    free(pys);
}


int binary_search(int *xs, int n, int x)
{
    int l = 0;
    int r = n;
    while (l < r)
    {
        int k = l + (r - l) / 2;
        int x0 = xs[k];
        if (x0 == x) {
            while (l < k && xs[k - 1] == x)
            {
                k--;
            }
            return k;
        } else if (x0 < x) {
            l = k + 1;
        } else { // x0 > x
            r = k;
        }
    }
    return n;
}


int main()
{
    int n;
    int *xs;
    
    puts("How many numbers do you want to search?");
    n = read_int();
    if (n < 0 || 15000 <= n) abort();
    xs = malloc(n * sizeof(int));
    if (xs == 0) abort();
    
    
    for (int i = 0; ; i++)
    {
        if (i >= n)
          break;
        int x = read_int();
        xs[i] = x;
    }
    
    merge_sort(xs, n);
    
    for (;;)
    {
        puts("Enter a number to search for, or -1 to quit.");
        int x = read_int();
        if (x == -1) break;
        int i = binary_search(xs, n, x);
        if (i == n) {
            puts("The number does not appear in the list.");
        } else {
            printf("%i", i);
            puts("");
        }
    }
    
    free(xs);
    return 0;
}
