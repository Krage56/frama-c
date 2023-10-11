// 3
#define UPPER_LIMIT 255

/*@ predicate Sorted(int *a, integer n) =
@   \forall integer i;
@   (0 <= i < n - 1 ==> a[i] <= a[i + 1]) || (0 <= n <= 1);
@*/
/*@
@   logic integer Sum{L}(int *a, integer n) = (n > 0) ? a[n - 1] + Sum{L}(a, n - 1) : 0;
@*/

/*@ predicate Increased{L1, L2}(int* arr, integer len) = 
@   Sum{L2}(arr, len) >= Sum{L1}(arr, len);
@*/

/*@
@   predicate Swapped{L1,L2}(int *a, integer i, integer j) =
@       \at(a[i],L1) == \at(a[j],L2) && 
@       \at(a[j],L1) == \at(a[i],L2) && 
@       \forall integer k; k != i && k != j 
@           ==> \at(a[k],L1) == \at(a[k],L2);
@*/

/*@
@ inductive Permuted{L1,L2}(int *arr, integer l, integer r) {
@       case Permuted_refl{L}:
@           \forall int *arr, integer l, r; Permuted{L,L}(arr, l, r);
@       case Permuted_sym{L1,L2}:
@           \forall int *arr, integer l, r; Permuted{L1,L2}(arr, l, r) ==> Permuted{L2,L1}(arr, l, r);
@       case Permuted_trans{L1,L2,L3}:
@           \forall int *arr, integer l, r; Permuted{L1,L2}(arr, l, r) && Permuted{L2,L3}(arr, l, r) ==> Permuted{L1,L3}(arr, l, r);
@       case Permuted_swap{L1,L2}:
@           \forall int *arr, integer l, r, i, j; l <= i <= r && l <= j <= r && Swapped{L1,L2}(arr, i, j) ==> Permuted{L1,L2}(arr, l, r);
@ }
@*/



/*@
@   requires \valid(arr + (0..n-1));
@   requires \forall integer i; 0 <= i <= n - 1 ==> 0 <= arr[i] <= UPPER_LIMIT;
@   assigns arr[0..n-1];
@   ensures Sorted(arr, n);
@   ensures Permuted{Old, Here}(arr, 0, n-1);
@*/
void count_pos(int *arr, int n) {
    int count[UPPER_LIMIT + 1];
    int i, j;
    /*@
    @ loop invariant (\forall integer k; 0 <= k < i ==> (count[k] == 0));
    @ loop invariant 0 <= i <= UPPER_LIMIT + 1;
    @ loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @ loop assigns count[0..UPPER_LIMIT], i;
    @ loop variant UPPER_LIMIT - i;
    @*/
    for (i = 0; i <= UPPER_LIMIT; ++i) {
        count[i] = 0;
    }

    /*@ 
    @   loop invariant \at(i, LoopEntry) == 0;
    @   loop invariant Increased{Pre, Here}(&count[0], UPPER_LIMIT + 1);
    @   loop invariant \forall integer k; 0 <= arr[k] <= UPPER_LIMIT ==> 0 <= count[i] < n;
    @   loop assigns count[0..UPPER_LIMIT], i;
    @   loop variant n - i;
    @*/   
    for (i = 0; i < n; ++i) {
        ++count[arr[i]];
        /*@
        @   assert Sum{Pre}(&count[0], UPPER_LIMIT + 1) < Sum{LoopCurrent}(&count[0], UPPER_LIMIT + 1);
        @*/
    }

    /*@
    @   loop invariant \at(i, LoopEntry) == 1;
    @   loop invariant 1 <= i <= UPPER_LIMIT + 1;
    @   loop assigns count[0..UPPER_LIMIT], i;
    @   loop variant UPPER_LIMIT + 1 - i;   
    @*/
    for (i = 1; i <= UPPER_LIMIT; ++i) {
        count[i] += count[i - 1];
    }

    /*@
    @   ghost int sort_counter = 0;
    @*/
    /*@
    @   assert \forall integer k; 0 <= k <= UPPER_LIMIT ==> 0 <= count[k] <= n;
    @*/
   
    /*@
    @   loop invariant \at(i, LoopEntry) == 0;
    @   loop invariant 0 <= i <= UPPER_LIMIT;
    @   loop assigns arr[0..n-1], i, j;
    @   loop variant UPPER_LIMIT - i;
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
        @   loop invariant Sorted(&arr[j], sort_counter);
        @   loop assigns arr[j..count[i] - 1];
        @   loop variant n - j;
        @*/
        for (; j < count[i]; ++j) {
            arr[j] = i;
            //@ ghost ++sort_counter;
        }
        //@ ghost sort_counter = 0;
    }

    /*@
    @   loop assigns arr[j..n-1], j;
    @   loop variant n - j;
    @*/
    for (j = count[UPPER_LIMIT]; j < n; ++j) {
        arr[j] = UPPER_LIMIT;
        //@ ghost ++sort_counter;
    }
}