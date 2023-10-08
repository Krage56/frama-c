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

    for (i = 0; i < UPPER_LIMIT; ++i) {
        for (j = count[i]; j < count[i + 1]; ++j) {
            arr[j] = i;
        }
    }
    for (j = count[UPPER_LIMIT]; j < n; ++j) {
        arr[j] = UPPER_LIMIT;
    }
}

#include <stdio.h>

int main(){
    int arr[5];
    arr[0] = 2;
    arr[1] = 3;
    arr[2] = 1;
    arr[3] = 1;
    arr[4] = 5;

    count_pos(&arr[0], 5);

    for(int i = 0; i < 5; ++i){
        printf("%d\n", arr[i]);
    }
    return 0;
}