from uclid5_api import IntegerSort, Module

__author__ = "FedericoAureliano"
__copyright__ = "FedericoAureliano"
__license__ = "MIT"


def test_simple():
    m = Module("test")
    x = m.declare_var("x", IntegerSort())
    y = m.declare_var("y", IntegerSort())
    m.init.assign(x, 0)
    m.init.assign(y, 0)
    m.next.assign(x, x + 1)
    m.next.assign(y, y + 1)
    m.assert_invariant("inv1", x < y)

    expected = """
        module test {
            var x: integer;
            var y: integer;
            init {
                x = 0;
                y = 0;
            }
            next {
                x' = x + 1;
                y' = y + 1;
            }
            invariant inv1: x < y;
        }
    """

    assert str(m).split() == expected.split()
