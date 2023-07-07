from uclid5_api import IntegerSort, Module

__author__ = "FedericoAureliano"
__copyright__ = "FedericoAureliano"
__license__ = "MIT"


def test_assigns():
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


def test_if():
    m = Module("test")
    x = m.declare_var("x", IntegerSort())
    m.init.assign(x, 0)

    then, else_ = m.next.condition(x == 0)
    then.assign(x, x + 1)
    else_.assign(x, x - 1)

    m.assert_invariant("inv1", x > 0)

    expected = """
        module test {
            var x: integer;
            init {
                x = 0;
            }
            next {
                if (x == 0) {
                    x' = x + 1;
                } else {
                    x' = x - 1;
                }
            }
            invariant inv1: x > 0;
        }
    """

    assert str(m).split() == expected.split()


test_if()
