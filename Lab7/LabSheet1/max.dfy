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
