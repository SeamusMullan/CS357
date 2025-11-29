// Student Number: 23434744
// Seamus Mullan, 2025

// Q1
/*
Write a method that computes the sum of the first n natural numbers without using multiplication and prove that the result is equal to the nth triangle number n(n+1)/2n(n+1)/2.
*/
method SumFirst(n: nat) returns (sum: nat)
    ensures sum == n * (n + 1) / 2
{
    sum := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n // basic bound for da loop
        invariant sum == i * (i + 1) / 2 // sum up to i
    {
        i := i + 1;
        sum := sum + i;
    }
}

// Q2
/*
The Fibonacci sequence begins with the numbers 0 and 1. To compute the next number in the sequence, sum the previous two. The sequence therefore continues as 0,1,1,2,3,5,8,…0,1,1,2,3,5,8,….
Write a method which iteratively computes the nth Fibonacci number without any recursive calls and verify that it is equal to the mathematical definition.
 */
function Fib(n: nat): nat
{
    if n < 2 then n else Fib(n - 1) + Fib(n - 2)
}
method FibIter(n: nat) returns (x: nat)
    ensures x == Fib(n)
{
    var i := 0;

    var a := 0;
    var b := 1;
    
    // loop until we get the nth num
    while i < n
        invariant 0 <= i <= n
        invariant a == Fib(i) // a is Fib(i)
        invariant b == Fib(i + 1) // b is Fib(i+1)
    {
        // swap and increment i
        var temp := a;
        a := b;
        b := temp + b;
        i := i + 1;
    }
    x := a;
}

// Q3
/*
Write and verify a method which finds the index pointing to the smallest element in an array. You might find it useful to look at the binary search pre- and postconditions from the previous lab.
*/
method Smallest(a: array<int>) returns (minIndex: nat)
ensures 0 <= minIndex < a.Length // tis in the array
ensures forall k :: 0 <= k < a.Length ==> a[minIndex] <= a[k] // make sure its the smallest by the end
{

    minIndex := 0; // inni de beninging, inni de, inni de bening.. inni de beninging........
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant 0 <= minIndex <= i // we cant have the index be in the future now can we
        invariant forall j :: 0 <= j < i ==> a[minIndex] < a[j] // make sure minIndex is smallest up to i
    {
        if a[i] < a[minIndex] {
            minIndex := i;
        }
        i := i + 1;
    }
    return minIndex;
}
// Q4
/*
Write a method Filter which takes an array aa and a predicate PP as arguments, then builds a sequence of all the elements in aa satisfying PP.
For example, if a = [1, 2, 3, 4] then Filter(a, IsEven) should return [2, 4].
Prove the following:
    All the elements of the output sequence satisfy PP.
    If the output sequence is empty, then no element in the array aa satisfied PP.
    The output sequence only contains elements from aa—that is, prove multiset(s) <= multiset(a[..]).

Explain in a comment above the method why this might not be enough to fully specify a filter method and ensure it works as intended.
*/

method Filter<T>(a: array<T>, P: T -> bool) returns (s: seq<T>)
{
    // todo
}