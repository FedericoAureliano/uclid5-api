from uclid5_api import Module, array, bitvector, integer


def test_assigns():
    m = Module("test")
    x = m.declare_var("x", integer())
    y = m.declare_var("y", integer())
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
    x = m.declare_var("x", integer())
    m.init.assign(x, 0)

    then, else_ = m.next.condition(x == 0)
    then.assign(x, x + 1)
    then2, else2 = else_.condition(x < 10)
    then2.assign(x, x - 1)
    else2.assign(x, x - 2)

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
                    if (x < 10) {
                        x' = x - 1;
                    } else {
                        x' = x - 2;
                    }
                }
            }
            invariant inv1: x > 0;
        }
    """

    assert str(m).split() == expected.split()


def test_array():
    m = Module("test")
    m.declare_var("x", array(integer(), integer()))

    expected = """
        module test {
            var x: [integer]integer;
        }
    """
    assert str(m).split() == expected.split()


def test_bitvector():
    m = Module("test")
    m.declare_var("x", bitvector(32))

    expected = """
        module test {
            var x: bv32;
        }
    """

    assert str(m).split() == expected.split()


test_bitvector()
