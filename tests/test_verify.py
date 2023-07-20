from uclid5_api import (
    Module,
    array,
    bitvector,
    datatype,
    enum,
    implies,
    induction,
    integer,
    negation,
    real,
    this,
)


def test_induction_good():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.init.assign(x, 0)
    m.next.assign(x, x + 1)
    m.assert_invariant("x_gte_0", x >= 0)

    assert induction(m) is True


def test_induction_bad():
    m = Module("fib")
    a = m.declare_var("a", integer())
    b = m.declare_var("b", integer())

    m.init.assign(a, 0)
    m.init.assign(b, 1)

    m.next.assign(a, b)
    m.next.assign(b, a + b)

    m.assert_invariant("b_gte_0", b >= 0)

    assert induction(m) is False


def test_array_good_induction():
    m = Module("test")
    x = m.declare_var("x", array(real(), bitvector(32)))
    y = m.declare_var("y", real())

    m.init.assign(x[y], 0)
    m.next.assign(x[y], 0)

    m.assert_invariant("x_at_y_is_0", x[y] == 0)

    assert induction(m) is True


def test_array_bad_induction():
    m = Module("test")
    x = m.declare_var("x", array(real(), bitvector(32)))
    y = m.declare_var("y", real())

    m.init.assign(y, 1)
    m.init.assign(x[y], 0)

    m.next.assign(y, 1)
    m.next.assign(x[y], 0)

    m.assert_invariant("x_at_y_is_0", x[y] == 0)

    assert induction(m) is False


def test_sequential_bad():
    m = Module("test")
    x = m.declare_var("x", integer())

    m.init.assign(x, 0)
    m.init.assign(x, x + 1)
    m.init.assign(x, x + 2)

    m.assert_invariant("x_eq_3", x == 4)

    assert induction(m) is False


def test_sequential_good():
    m = Module("test")
    x = m.declare_var("x", integer())

    m.init.assign(x, 0)
    m.init.assign(x, x + 1)
    m.init.assign(x, x + 2)

    m.assert_invariant("x_eq_3", x == 3)

    assert induction(m) is True


def test_sequential_if_good():
    m = Module("test")
    x = m.declare_var("x", integer())

    m.init.assign(x, 0)
    then_, else_ = m.init.branch(x == 0)
    then_.assign(x, x + 1)
    else_.assign(x, x + 2)
    m.init.assign(x, x * 7)

    m.assert_invariant("x_eq_7", x == 7)
    assert induction(m) is True


def test_sequential_if_bad():
    m = Module("test")
    x = m.declare_var("x", integer())

    m.init.assign(x, 0)
    then_, else_ = m.init.branch(x != 0)
    then_.assign(x, x + 1)
    else_.assign(x, x + 2)
    m.init.assign(x, x * 7)

    m.assert_invariant("x_eq_7", x == 7)
    assert induction(m) is False


def test_adt_good():
    m = Module("test")
    t, cons, nil, head, _, is_cons, is_nil = datatype(
        "list", ("cons", [("head", integer()), ("tail", this())]), ("nil", [])
    )

    z = m.declare_var("z", t)

    m.init.assign(z, nil())

    then_, else_ = m.next.branch(is_cons(z))
    then_.assign(z, cons(head(z), z))
    else_.assign(z, cons(1, nil()))

    m.assert_invariant("head_is_always_1", implies(negation(is_nil(z)), head(z) == 1))
    assert induction(m) is True


def test_adt_bad():
    m = Module("test")
    t, cons, nil, head, _, is_cons, _ = datatype(
        "list", ("cons", [("head", integer()), ("tail", this())]), ("nil", [])
    )

    z = m.declare_var("z", t)

    m.init.assign(z, nil())

    then_, else_ = m.next.branch(is_cons(z))
    then_.assign(z, cons(head(z), z))
    else_.assign(z, cons(1, nil()))

    m.assert_invariant("head_is_always_1", head(z) == 1)
    assert induction(m) is False


def test_havoc_bad():
    m = Module("test")
    x = m.declare_var("x", integer())

    m.init.assign(x, 0)
    m.init.havoc(x)

    m.assert_invariant("x_eq_0", x == 0)

    assert induction(m) is False


def test_havoc_good():
    m = Module("test")
    d, a, b = enum("A", "B")
    z = m.declare_var("z", array(d, integer()))
    x = m.declare_var("x", d)

    m.init.assign(z[a], 0)
    m.init.assign(z[b], 0)

    m.init.havoc(x)

    m.assert_invariant("z_at_x_is_0", z[x] == 0)

    assert induction(m) is True
