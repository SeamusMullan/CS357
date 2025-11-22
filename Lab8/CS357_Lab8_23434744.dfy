
// CS357 Lab 8
// Student Number: 23434744

// --------------------------------------------------------------------
// Question 1: rewrite min and max
// --------------------------------------------------------------------
function MaxDef(a: int, b: int): int
{
    if a > b then a else b
}

method Max(a: int, b: int) returns (m: int)
ensures MaxDef(a, b) == m
{
    if a >= b {
        m := a;
    } else {
        m := b;
    }
}

method {:test} TestMax()
{
    var x := Max(2, 3);
    assert x == 3;

    var y := Max(-4, 1);
    assert y == 1;

    var z := Max(0, 0);
    assert z == 0;
}

function MinDef(a: int, b: int): int
{
    if a <=b then a else b
}


method Min(a: int, b: int) returns (m: int)
ensures MinDef(a, b) == m
{
    if a <= b {
        m := a;
    } else {
        m := b;
    }
}

method {:test} TestMin()
{
    var x := Min(2, 3);
    assert x == 2;

    var y := Min(-4, 1);
    assert y == -4;

    var z := Min(0, 0);
    assert z == 0;
}


// --------------------------------------------------------------------
// Question 2: write a function to compute 2^n
// --------------------------------------------------------------------
function pow2(n: nat): nat
    decreases n
{
    if n == 0 then
        1 // base case
    else
        2 * pow2(n - 1)
}

function powN(a: int, n: nat): int
    decreases n
{
    if n == 0 then
        1 // base case
    else
        a * powN(a, n - 1)
}

// --------------------------------------------------------------------
// Question 3: function to compute a^n
// --------------------------------------------------------------------
method Pow(a: int, n: nat) returns (result: int)
ensures result == powN(a, n)
{
    result := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result == powN(a, i) // since result should be = to a^i when were on the ith loop
    {
        result := result * a;
        i := i + 1;
    }
    return result;
}

// --------------------------------------------------------------------
// Question 4: write a function to compute gcd
// --------------------------------------------------------------------
function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    decreases a + b // since we decrease a or b every time, its gotta get smoller
{
    if a == b then
      a
    else if b > a then
      gcd(b - a, a)
    else
      gcd(b, a - b)
}

// --------------------------------------------------------------------
// Question 5: write a predicate to check if an array is sorted
// nb use "forall x, y | P :: Q"
// a.k.a For all x and y such that P, we have Q
// --------------------------------------------------------------------
predicate sorted(a: array<int>)
    reads a
{
    // for everything, where indexes are IN the array (not over a.Length)
    // for all a[i] there exists an a[j] where i < j and a[i] <= a[j]
    forall i, j | 0 <= i < j < a.Length :: a[i] <= a[j]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
    requires sorted(a)
    ensures index == -1 || 0 <= index < a.Length
    ensures index == -1 ==> forall k | 0 <= k < a.Length :: a[k] != value // we couldnt find it
    ensures index >= 0  ==> a[index] == value // we found it at the index, since we know it, we just check that its actually right

{
    var low := 0;
    var high := a.Length;

    while low < high
        invariant 0 <= low <= high <= a.Length
        invariant value !in a[..low] && value !in a[high..]
    {
        var mid := (high + low) / 2;

        if a[mid] < value {
            low := mid + 1;
        } else if a[mid] > value {
            high := mid;
        } else {
            return mid;
        }
    }
    index := -1;
}