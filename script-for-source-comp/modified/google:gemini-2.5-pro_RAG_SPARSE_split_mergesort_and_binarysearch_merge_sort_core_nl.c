

void merge_sort_core(int *pxs, int *pys, int n)
{
    if (n >= 2) {
        int nleft = n / 2;
        int nright = n - n / 2;
        int *left = pxs;
        int *right = pxs + nleft;


        merge_sort_core(left, pys, nleft);

        merge_sort_core(right, pys + nleft, nright);


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
        
        
        for (int p = 0; ; )
        {
            if (p >= n) break;
            pxs[p] = pys[p];
            p++;
        }
    } else {
    }
}
