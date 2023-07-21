from uclid5_api import (
    Module,
    array,
    bitvector,
    bmc,
    boolean,
    datatype,
    enum,
    implies,
    induction,
    integer,
    negation,
    real,
    this,
)
from uclid5_api.types import record


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


def test_bmc_good():
    m = Module("test")
    x = m.declare_var("x", integer())

    m.init.assign(x, 0)

    m.next.assign(x, x + 1)

    m.assert_invariant("x_lt_3", x < 3)

    assert bmc(m, 2) is True


def test_bmc_bad():
    m = Module("test")
    x = m.declare_var("x", integer())

    m.init.assign(x, 0)

    m.next.assign(x, x + 1)

    m.assert_invariant("x_lt_3", x < 3)

    assert bmc(m, 5) is False


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


def test_record_assign_good():
    m = Module("test")
    r, _, left, right = record(("left", integer()), ("right", integer()))
    x = m.declare_var("x", r)

    m.init.assign(left(x), 0)
    m.next.assign(right(x), right(x) + 1)

    m.assert_invariant("left_is_0", left(x) == 0)

    assert induction(m) is True
    assert bmc(m, 5) is True


def test_blockworld_no_ctx():
    m = Module("blockworld")
    block, a, b, c, d = enum("Q", "W", "R", "T")
    tower, stack, empty, top, rest, is_stack, _ = datatype(
        "tower", ("stack", [("top", block), ("rest", this())]), ("empty", [])
    )

    x = m.declare_var("x", tower)
    y = m.declare_var("y", tower)
    choice = m.declare_var("choice", boolean())

    the_tower = stack(a, stack(b, stack(c, stack(d, empty()))))

    m.init.assign(x, the_tower)
    m.init.assign(y, empty())

    m.next.havoc(choice)
    then_, else_ = m.next.branch(choice)

    rest_x, _ = then_.branch(is_stack(x))
    rest_x.assign(y, stack(top(x), y))
    rest_x.assign(x, rest(x))

    rest_y, _ = else_.branch(is_stack(y))
    rest_y.assign(x, stack(top(y), x))
    rest_y.assign(y, rest(y))

    print(m)

    m.assert_invariant("negated_goal", y != the_tower)

    # It shouldn't be possible to move from x to y and have y
    # be the same as the original tower at x.
    # Therefore, the invariant (the negation of the goal) should hold
    assert bmc(m, 5) is True


def test_blockworld_yes_ctx():
    m = Module("blockworld")
    block, a, b, c, d = enum("A", "B", "C", "D")
    tower, stack, empty, top, rest, _, _ = datatype(
        "tower", ("stack", [("top", block), ("rest", this())]), ("empty", [])
    )

    x = m.declare_var("x", tower)
    y = m.declare_var("y", tower)
    choice = m.declare_var("choice", boolean())

    the_tower = stack(a, stack(b, stack(c, stack(d, empty()))))
    the_reversed_tower = stack(d, stack(c, stack(b, stack(a, empty()))))

    m.init.assign(x, the_tower)
    m.init.assign(y, empty())

    m.next.havoc(choice)
    then_, else_ = m.next.branch(choice)
    then_.assign(y, stack(top(x), y))
    then_.assign(x, rest(x))
    else_.assign(x, stack(top(y), x))
    else_.assign(y, rest(y))

    m.assert_invariant("negated_goal", y != the_reversed_tower)

    # It should be possible to move from x to y and have y be
    # the reverse of the original tower at x.
    # Therefore, the invariant (the negation of the goal) should be violated
    assert bmc(m, 5) is False
