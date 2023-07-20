from uclid5_api import (
    Module,
    array,
    bitvector,
    datatype,
    enum,
    integer,
    prime,
    real,
    record,
    sort,
    this,
)


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

    then1, else1 = m.next.branch(x == 0)
    then1.assign(x, x + 1)
    then2, else2 = else1.branch(x < 10)
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


def test_array_sort():
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


def test_bitvector2():
    m = Module("test")
    x = m.declare_var("x", bitvector(32))
    m.init.assign(x, 0)

    expected = """
        module test {
            var x: bv32;
            init {
                x = 0bv32;
            }
        }
    """

    assert str(m).split() == expected.split()


def test_prime():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.next.assign(x, prime(x) + 1)

    expected = """
        module test {
            var x: integer;
            next {
                x' = x' + 1;
            }
        }
    """

    assert str(m).split() == expected.split()


def test_array_assign():
    m = Module("test")
    x = m.declare_var("x", array(real(), bitvector(32)))
    y = m.declare_var("y", real())

    m.next.assign(x[y], 0)

    expected = """
        module test {
            var x: [real]bv32;
            var y: real;
            next {
                x'[y] = 0bv32;
            }
        }
    """
    assert str(m).split() == expected.split()


def test_real():
    m = Module("test")
    y = m.declare_var("y", real())

    m.next.assign(y, 0)

    expected = """
        module test {
            var y: real;
            next {
                y' = 0.0;
            }
        }
    """
    assert str(m).split() == expected.split()


def test_enum():
    m = Module("test")
    t, a, _, _ = enum("A", "B", "C")
    y = m.declare_var("y", t)

    m.next.assign(y, a)

    expected = """
        module test {
            var y: enum {A, B, C};
            next {
                y' = A;
            }
        }
    """

    assert str(m).split() == expected.split()


def test_record():
    m = Module("test")
    (
        t,
        c,
        select_x,
        _,
    ) = record(("x", integer()), ("y", integer()))
    z = m.declare_var("z", t)

    m.init.assign(z, c(1, 2))
    m.next.assign(select_x(z), 0)

    expected = """
        module test {
            var z: record {x: integer, y: integer};
            init {
                z = {x = 1, y = 2};
            }
            next {
                z'.x = 0;
            }
        }
    """
    assert str(m).split() == expected.split()


def test_datatype():
    m = Module("test")
    t, cons, nil, head, tail, is_cons, _ = datatype(
        "list", ("cons", [("head", integer()), ("tail", this())]), ("nil", [])
    )

    z = m.declare_var("z", t)

    m.init.assign(z, cons(1, nil()))

    m.next.assign(z, cons(head(z), tail(z)))

    m.assert_invariant("inv1", is_cons(z))

    expected = """
        module test {
            var z: datatype list = {cons(head: integer, tail: this) | nil};
            init {
                z = cons(1, nil);
            }
            next {
                z' = cons(z.head, z.tail);
            }
            invariant inv1: z is cons;
        }
    """
    print(m)
    assert str(m).split() == expected.split()


def test_usort():
    m = Module("test")
    m.declare_var("x", sort("A"))

    expected = """
        module test {
            var x: A;
        }
    """
    assert str(m).split() == expected.split()


def test_havoc():
    m = Module("test")
    x = m.declare_var("x", integer())
    m.init.havoc(x)

    expected = """
        module test {
            var x: integer;
            init {
                havoc x;
            }
        }
    """

    assert str(m).split() == expected.split()
