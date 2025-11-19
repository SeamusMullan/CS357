
// CS357 Lab 7
// Student Number: 23434744

// --------------------------------------------------------------------
// Question 1
// --------------------------------------------------------------------

method Max(a: int, b: int) returns (m: int)
ensures m >= a && m >= b
ensures m == a || m == b
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

// --------------------------------------------------------------------
// Question 2
// --------------------------------------------------------------------

method Min(a: int, b: int) returns (m: int)
ensures m <= a && m <= b
ensures m == a || m == b
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
// Question 3
// --------------------------------------------------------------------

/*
this method uses recursion to multiply a number x by y
if x is 0, the result is 0 (duh)
if x is negative, we call the method again with -x and then negate the result, so we can just use the code for positive numbers
*/
method M1(x: int, y: int) returns (r: int)
    ensures r == x * y
    decreases x < 0, x
{
    if x == 0 {
        r := 0; // base case: M1(0, y) = 0
    } else if x < 0 {
        // when x is negative we can change the sign and call the function again. then minus 1 since binary range is like -128 -> 127 etc.
        r := M1(-x, y);
        r := -r;
    } else {
        // recursively make x smaller, call this again and then add y to the result
        // basically this is just multiplication
        r := M1(x - 1, y);
        r := A1(r, y);
    }
}

/**
This method adds two integers x and y together.
used above to add `y` to `r` a bunch (x times)
 */
method A1(x: int, y: int) returns (r: int)
    ensures r == x + y
{
    // start with r equal to x
    r := x;
    if y < 0 {
        var n := y;
        // decrement r and increment n until n is 0, ensure x+y-n stays the same
        while n != 0
            invariant r == x + y - n
            invariant -n >= 0
        {
            r := r - 1;
            n := n + 1;
        }
    } else {
        var n := y;
        // same as above loop but incrementing r and decrementing n
        while n != 0
            invariant r == x + y - n
            invariant n >= 0
        {
            r := r + 1;
            n := n - 1;
        }
    }

    // at the end, r == x + y - 0, so r == x + y
    // basically this is just adding stuff

}

// --------------------------------------------------------------------
// Question 4
// --------------------------------------------------------------------

method swap(a: array<int>, i: nat, j: nat)
    modifies a

    // requires relationship between i and a.Length
    // requires relationship between j and a.Length

    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{
    // todo
}

method {:main} TestSwap()
{
    var a := new int[] [1, 2, 3, 4];

    assert a[1] == 2 && a[3] == 4;
    swap(a, 1, 3);
    assert a[1] == 4 && a[3] == 2;
}

