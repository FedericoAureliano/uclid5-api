from uclid5_api import IntegerSort, Module, step

__author__ = "FedericoAureliano"
__copyright__ = "FedericoAureliano"
__license__ = "MIT"


def test_step():
    m = Module("test")
    x = m.declare_var("x", IntegerSort())
    m.init.assign(x, x + 1)

    xp = step(m.vars, m.init)["x"]

    print(xp)
    assert xp == x + 1


test_step()
