// 3
#define UPPER_LIMIT 255

/*@ predicate Sorted(int *a, integer n) =
@   \forall integer i;
@   (0 <= i < n - 1 ==> a[i] <= a[i + 1]);
@*/

/*@
@   logic integer Sum{L}(int *a, integer n) = (n > 0) ? \at(a[n - 1], L) + Sum{L}(a, n - 1) : 0;
@*/


/*@
    predicate RightUnchange{L1, L2}(int* arr, int* count, integer n, integer limit, integer i) = \forall integer k; \at(count[i], L2) <= k <= n ==> \at(arr[k], L2) == \at(arr[k], L2);
@*/

/*@
@   logic integer Count(int* arr, integer len, integer elem) = (len == 0) ? 0 : (arr[len - 1] == elem) ? 1 + Count(arr, len - 1, elem) : Count(arr, len - 1, elem); 
@*/

/*@
@   lemma spec_linear_sum{L1, L2}:
    \forall int *a, integer k, n;
    0 <= k < n
    && (\forall integer i; 0 <= i < n && i != k ==> \at(a[i], L1) == \at(a[i],L2))
    && \at(a[k], L2) == \at(a[k], L1) + 1
        ==> Sum{L2}(a, n) == Sum{L1}(a, n) + 1;
@*/

/*@
    predicate SumIncrementConditions{L1, L2}(int arr_i, int* count) = (\at(count[arr_i], L2) == 1 + \at(count[arr_i], L1)) && (\forall integer l; 
            (0 <= l <= UPPER_LIMIT && l != arr_i) ==> (\at(count[l], L1) == \at(count[l], L2)));
@*/

/*@
@   predicate Swapped{L1,L2}(int *a, integer i, integer j) =
@       \at(a[i],L1) == \at(a[j],L2) && 
@       \at(a[j],L1) == \at(a[i],L2) && 
@       \forall integer k; k != i && k != j 
@           ==> \at(a[k],L1) == \at(a[k],L2);
@*/

/*@
   axiomatic Unchanged
   {
        predicate Unchanged{K,L}(int* a, integer m, integer n) = \forall integer i; m <= i < n ==> \at(a[i], K) == \at(a[i], L);

        predicate Unchanged{K,L}(int* a, integer n) = Unchanged{K,L}(a, 0, n);
   }
*/



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
    @ loop invariant \at(i, LoopEntry) == 0;
    @ loop invariant (\forall integer k; (0 <= k < i) ==> (count[k] == 0));
    @ loop invariant 0 <= i <= UPPER_LIMIT + 1;
    @ loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @ loop assigns count[0..UPPER_LIMIT], i;
    @ loop variant UPPER_LIMIT - i;
    @*/
    for (i = 0; i <= UPPER_LIMIT; ++i) {
        /*@
            assert \forall integer k; (0 <= k < i) ==> (count[k] == 0); 
        @*/
        count[i] = 0;
        /*@ 
            assert count[i] == 0;
        @*/
        /*@
            assert \forall integer j; (0 <= j <= i) ==> (count[j] == 0);
        @*/
    }
    /*@
        assert \forall integer k; (0 <= k <= UPPER_LIMIT) ==> (count[k] == 0);
    @*/
    /*@ 
    @   loop invariant \at(i, LoopEntry) == 0;
    @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @   loop invariant \forall integer j; (0 <= j < n) ==> (0 <= arr[j] <= UPPER_LIMIT);
    @   loop invariant \forall integer j; (0 <= j <= UPPER_LIMIT) ==> (count[j] >= 0); 
    @   loop invariant \forall integer j; (0 <= j < n) ==> \valid(&count[0] + (arr[j]));
    @   loop assigns count[0..UPPER_LIMIT], i;
    @   loop variant n - i;
    @*/   
    for (i = 0; i < n; ++i) {
        //@ assert (0 <= arr[i] <= UPPER_LIMIT) ==> (count[arr[i]] >= 0);
        ++count[arr[i]];
        /*@
            assert count[arr[i]] == 1 + \at(count[arr[i]], LoopCurrent);
        @*/
        /*@ 
            assert ((\at(count[arr[i]], LoopCurrent) >= 0) && (\at(count[arr[i]], LoopCurrent) == count[arr[i]] - 1)) ==> (count[arr[i]] >= 0);
        @*/
        /*@
            assert (count[arr[i]] == 1 + \at(count[arr[i]], LoopCurrent)) ==> (count[arr[i]] != \at(count[arr[i]], LoopCurrent)); 
        @*/
        /*@
            assert \forall integer l; 
            (0 <= l <= UPPER_LIMIT && l != arr[i]) ==> (count[l] == \at(count[l], LoopCurrent));
        @*/
        //@ assert SumIncrementConditions{LoopCurrent, Here}(arr[i], &count[0]);
        /*@
            assert SumIncrementConditions{LoopCurrent, Here}(arr[i], &count[0]) ==> (Sum{Here}(&count[0], UPPER_LIMIT + 1) == 1 + Sum{LoopCurrent}(&count[0], UPPER_LIMIT + 1));
        @*/
    }
    /*@
    @   loop invariant \at(i, LoopEntry) == 1;
    @   loop invariant 1 <= i <= UPPER_LIMIT + 1;
    @   loop invariant (1 <= i <= UPPER_LIMIT + 1) ==> (count[i-1] == Sum(\at(&count[0], LoopEntry), i));
    @   loop invariant \forall integer k; (0 <= k <= UPPER_LIMIT) ==> (count[k] >= 0);
    @   loop invariant (1 <= i <= UPPER_LIMIT + 1) ==> (count[i-1] >= 0); 
    @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @   loop variant UPPER_LIMIT + 1 - i;   
    @*/

    for (i = 1; i <= UPPER_LIMIT; ++i) {
        /*@
        assert count[i-1] >= 0;
        @*/
        count[i] += count[i - 1];
        /*@ 
        assert ((count[i-1] >= 0) && (\at(count[i], LoopCurrent) >= 0) && (count[i] == count[i-1] + \at(count[i], LoopCurrent))) ==> (count[i] >= 0);
        @*/
        /*@ 
        assert (count[i] == count[i-1] + \at(count[i], LoopCurrent));
        @*/
        /*@ 
        assert (count[i] == count[i-1] + \at(count[i], LoopCurrent)) ==> (count[i] == Sum(\at(&count[0], LoopCurrent), i+1));
        @*/
    }
    /*@
        assert \forall integer j; (0 <= j <= UPPER_LIMIT) ==> (count[j] >= 0);
    @*/
    /*@
    @   loop invariant \at(i, LoopEntry) == 0;
    @   loop invariant 0 <= i <= UPPER_LIMIT;
    @   loop invariant RightUnchange{Pre, Here}(arr, &count[0], n, UPPER_LIMIT, i);
    @   loop invariant \forall integer k; (0 < k <= UPPER_LIMIT ==> count[k] >= 0);
    @   loop assigns arr[0..n-1], i, j;
    @   loop variant UPPER_LIMIT - i;
    @*/  
    for (i = 0; i < UPPER_LIMIT; ++i) {
        /*@
        @   assert ((i > 0) ==> (j == count[i-1] >= 0)) || ((i == 0) ==> (j == 0));
        @*/
        j = (i > 0) ? count[i - 1] : 0;
        /*@
        @   assert \forall integer k; (0 <= k <= UPPER_LIMIT) ==> (0 <= count[k] <= n);
        @*/
        /*@
        @   assert (0 <= j <= n);
        @*/
        /*@
        @   loop invariant 0 <= i <= UPPER_LIMIT;
        @   loop invariant RightUnchange{Pre, Here}(arr, &count[0], n, UPPER_LIMIT, i);
        @   loop invariant \forall integer k; (0 <= k < j) ==> (arr[k] <= i);
        @   loop invariant \forall integer k; (0 < k < j) ==> (arr[k - 1] <= arr[k]);
        @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
        @   loop assigns arr[j..count[i] - 1];
        @   loop variant n - j;
        @*/
        for (; j < count[i]; ++j) {
            arr[j] = i;
            //@ assert (arr[j] == i) ==> (arr[j] <= i);
            /*@
                assert (j > 0) ==> (arr[j] >= arr[j-1]);
            @*/
            //@ assert Unchanged{LoopEntry, Here}(arr, count[i], n);
        }
        
        //@ assert Sorted(\at(arr, Here), j - 1);
        //How to show equality of Unchanged and invariant?
        /*@
        @   assert \forall integer k; (count[i] <= k <= n) ==> \at(arr[k], Pre) == arr[k];
        @*/
    }

    /*@
    @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @   loop invariant Sorted(arr, j);
    @   loop assigns arr[j..n-1], j;
    @   loop variant n - j;
    @*/
    for (j = count[UPPER_LIMIT]; j < n; ++j) {
        arr[j] = UPPER_LIMIT;
        /*@
            assert Sorted(arr, j);
        @*/
    }
}