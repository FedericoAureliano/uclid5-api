import z3

from uclid5_api import Module, bmc, induction, integer, step


def test_step_sequential():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.init.assign(x, x + 1)
    m.init.assign(x, x + 1)

    xp = step(m.vars, m.init)[x]
    assert xp == x + 1 + 1


def test_step_concurent():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.next.assign(x, x + 1)
    m.next.assign(x, x + 1)

    xp = step(m.vars, m.next)[x]
    assert xp == x + 1


def test_step_if():
    m = Module("test")
    x = m.declare_var("x", integer())
    then, else_ = m.init.condition(x > 0)
    then.assign(x, x - 1)
    else_.assign(x, x + 1)

    xp = step(m.vars, m.init)[x]
    assert xp == z3.If(x > 0, x - 1, x + 1)


def test_bmc_good():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.init.assign(x, 0)
    m.next.assign(x, x + 1)
    m.assert_invariant("x_gte_0", x >= 0)

    assert bmc(m, 10) is True


def test_bmc_bad():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.init.assign(x, 0)
    m.next.assign(x, x + 1)
    m.assert_invariant("x_lt_5", x < 5)

    assert bmc(m, 10) is False


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
