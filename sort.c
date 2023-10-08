// 3
#define UPPER_LIMIT 255

/*@ predicate Sorted(int *a, integer n) =
@   \forall integer i;
@   0 <= i < n - 1 ==> a[i] <= a[i + 1];
@*/

/*@
@   logic integer Sum(int *a, integer n) = (n > 0) ? a[n - 1] + Sum(a, n - 1) : 0;
@*/

/*@
@   requires \valid(arr + (0..n-1));
@   requires \forall integer i; 0 <= i <= n - 1 ==> 0 <= arr[i] <= UPPER_LIMIT;
@   assigns arr[0..n-1];
@   ensures Sorted(arr, n);
@*/
void count_pos(int *arr, int n) {
    int count[UPPER_LIMIT + 1];
    int i, j;
    /*@
    @ loop variant UPPER_LIMIT - i;
    @*/
    for (i = 0; i <= UPPER_LIMIT; ++i) {
        count[i] = 0;
    }

    /*@ 
    @   loop assigns count[0..UPPER_LIMIT], i;
    @   loop variant n - Sum(&count[0], UPPER_LIMIT + 1);
    @*/   
    for (i = 0; i < n; ++i) {
        ++count[arr[i]];
    }

    /*@
    @   loop assigns count[0..UPPER_LIMIT], i;
    @   loop variant n - count[i];   
    @*/
    for (i = 1; i <= UPPER_LIMIT; ++i) {
        count[i] += count[i - 1];
    }

    /*@
    @   ghost int sort_counter = 0;
    @*/
    /*@
    @   loop assigns arr[0..n-1], i, j;
    @   loop variant Sum(&count[i], UPPER_LIMIT - i + 1);
    @*/  
    for (i = 0; i < UPPER_LIMIT; ++i) {
        /*@
        @   assert (i <= 0) || ((i > 0) && (0 <= count[i-1] <= n));
        @*/
        j = (i > 0) ? count[i - 1] : 0;
        /*@
        @   assert (0 <= j <= n);
        @*/
        /*@
        @   loop assigns arr[j..count[i] - 1];
        @   loop invariant Sorted(arr, sort_counter + 1);
        @*/
        for (; j < count[i]; ++j) {
            arr[j] = i;
            //@ ghost ++sort_counter;
        }
    }
    for (j = count[UPPER_LIMIT]; j < n; ++j) {
        arr[j] = UPPER_LIMIT;
    }
}