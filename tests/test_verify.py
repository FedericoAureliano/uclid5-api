from uclid5_api import Module, integer, step


def test_step():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.init.assign(x, x + 1)

    xp = step(m.vars, m.init)["x"]

    print(xp)
    assert xp == x + 1


test_step()
