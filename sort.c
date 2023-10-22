// 3
#define UPPER_LIMIT 255

/*@ predicate Sorted(int *a, integer n) =
@   \forall integer i;
@   (0 <= i < n - 1 ==> a[i] <= a[i + 1]);
@*/

/*@
@   logic integer Sum{L}(int *a, integer n) = (n > 0) ? \at(a[n - 1], L) + Sum{L}(a, n - 1) : 0;
@*/

/*@ghost
@ /@lemma
@ @ requires 0 <= i <= n-1;
@ @ requires \valid(arr + (0..n-1));
@ @ decreases (n - i);
@ @ ensures ((i == n-1) ==> (Sum(arr, n) == Sum(arr, i) + arr[i]));
@ @/
@void sum_proof1(int* arr, int i, int n){
@     if (i != n - 1)
@       sum_proof1(arr, i+1, n);
@}*/


/*@
    predicate RightUnchange{L1, L2}(int* arr, int* count, integer n, integer limit, integer i) = \forall integer k; \at(count[i], L2) <= k <= n ==> \at(arr[k], L2) == \at(arr[k], L2);
@*/
/*@
@   lemma linear_sum{l}:
        \forall int* arr, integer n, integer i; 
        (((0 <= i <= n-1) && Sum(arr, 0) == 0) ==> (Sum(arr, n) == Sum(arr, i) + arr[i] + Sum(arr + i + 1, n - i - 1)));
@*/


/*@
@   lemma spec_linear_sum{l}:
    \forall int* a, int* b, integer l, integer n; \exists integer j; 
    (((0 <= l < n) && (0 <= j < n) && (l != j)) ==> ((a[j] == b[j] + 1) && (a[l] == b[l]))) ==>
    Sum(a, n) == Sum(a, j) + Sum(a + j + 1, n - j - 1) + a[j] == Sum(b, j) + Sum(b + j + 1, n - j - 1) + b[j] + 1 == Sum(b, n) + 1;
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
        //@ assert count[i] == 0;
    }
    /*@ 
    @   loop invariant \at(i, LoopEntry) == 0;
    @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @   loop invariant \forall integer j; (0 <= j < n ==> 0 <= arr[j] <= UPPER_LIMIT);
    @   loop invariant \forall integer j; 0 <= j <= UPPER_LIMIT ==> count[j] >= 0; 
    @   loop invariant \forall integer j; 0 <= j < n ==> \valid(&count[0] + (arr[j]));
    @   loop assigns count[0..UPPER_LIMIT], i;
    @   loop variant n - i;
    @*/   
    for (i = 0; i < n; ++i) {
        ++count[arr[i]];
        //@ assert (0 <= arr[j] <= UPPER_LIMIT) ==> count[arr[j]] >= 0;
        /*@
            assert count[arr[i]] == 1 + \at(count[arr[i]], LoopCurrent);
        @*/
        /*@
            assert \forall integer l; (0 <= l < arr[i] ==> count[l] == \at(count[l], LoopCurrent));
        @*/
        /*@
            assert \forall integer l; (arr[i] < l <= UPPER_LIMIT ==> count[l] == \at(count[l], LoopCurrent));
        @*/
        /*@
            assert
             (count[arr[i]] == 1 + \at(count[arr[i]], LoopCurrent)) ==> (Sum{Here}(&count[0], UPPER_LIMIT + 1) == 1 + Sum{LoopCurrent}(&count[0], UPPER_LIMIT + 1));
        @*/
    }
    /*@
    @   loop invariant \at(i, LoopEntry) == 1;
    @   loop invariant 1 <= i <= UPPER_LIMIT + 1;
    @   loop invariant 1 <= i <= UPPER_LIMIT + 1 ==> count[i-1] == Sum(\at(&count[0], LoopEntry), i);
    @   loop invariant 1 <= i <= UPPER_LIMIT + 1 ==> count[i-1] >= 0; 
    @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @   loop variant UPPER_LIMIT + 1 - i;   
    @*/

    for (i = 1; i <= UPPER_LIMIT; ++i) {
        count[i] += count[i - 1];
        /*@ 
        assert \at(count[i], LoopCurrent) >= 0;
        @*/
        /*@ 
        assert (count[i] == count[i-1] + \at(count[i], LoopCurrent));
        @*/
        /*@ 
        assert count[i] == Sum(\at(&count[0], LoopCurrent), i+1);
        @*/
    }
    /*@
        assert \forall integer j; 0 <= j <= UPPER_LIMIT && count[j] >= 0;
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
        @   assert (i <= 0) || ((i > 0) && (0 <= count[i-1] <= n));
        @*/
        j = (i > 0) ? count[i - 1] : 0;
        /*@
        @   assert \forall integer k; 0 <= k <= UPPER_LIMIT ==> 0 <= count[k] <= n;
        @*/
        /*@
        @   assert (0 <= j <= n);
        @*/
        /*@
        @   loop invariant 0 <= i <= UPPER_LIMIT;
        @   loop invariant RightUnchange{Pre, Here}(arr, &count[0], n, UPPER_LIMIT, i);
        @   loop invariant \forall integer k; 0 < k < j ==> arr[k] <= i;
        @   loop invariant \forall integer k; 0 < k < j ==> arr[k - 1] <= arr[k];
        @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
        @   loop assigns arr[j..count[i] - 1];
        @   loop variant n - j;
        @*/
        for (; j < count[i]; ++j) {
            arr[j] = i;
            //@ assert arr[j] == i;
            //@ assert Unchanged{Pre, Here}(arr, count[i], n);
        }
        
        //@ assert Sorted(\at(arr, Here), j - 1);
        //How to show equality of Unchanged and invariant?
        //@ assert Unchanged{Pre, Here}(arr, count[i], n);
        /*@
        @   assert \forall integer k; count[i] <= k <= n && \at(arr[k], Pre) == arr[k];
        @*/
        Lol:
    }

    /*@
    @   loop invariant \valid(&count[0] + (0..UPPER_LIMIT));
    @   loop invariant Sorted(arr, j);
    @   loop assigns arr[j..n-1], j;
    @   loop variant n - j;
    @*/
    for (j = count[UPPER_LIMIT]; j < n; ++j) {
        arr[j] = UPPER_LIMIT;
    }
}