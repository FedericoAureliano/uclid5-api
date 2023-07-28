from uclid5_api import (
    Module,
    array,
    bitvector,
    boolean,
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
    t, variants = enum("A", "B", "C")
    a = variants[0]
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
    t, c, ss = record(("x", integer()), ("y", integer()))
    select_x = ss[0]
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
    t, cs, ss, ts = datatype(
        "list", ("cons", [("head", integer()), ("tail", this())]), ("nil", [])
    )
    cons = cs[0]
    nil = cs[1]
    head = ss[0]
    tail = ss[1]
    is_cons = ts[0]

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


def test_blockworld():
    m = Module("blockworld")
    block, variants = enum("S", "D", "F", "G")
    a = variants[0]
    b = variants[1]
    c = variants[2]
    d = variants[3]
    tower, cs, ss, _ = datatype(
        "tower", ("stack", [("top", block), ("rest", this())]), ("empty", [])
    )
    stack = cs[0]
    empty = cs[1]
    top = ss[0]
    rest = ss[1]

    x = m.declare_var("x", tower)
    y = m.declare_var("y", tower)
    choice = m.declare_var("choice", boolean())

    the_tower = stack(a, stack(b, stack(c, stack(d, empty()))))

    m.init.assign(x, the_tower)
    m.init.assign(y, empty())

    m.next.havoc(choice)
    then_, else_ = m.next.branch(choice)
    then_.assign(y, stack(top(x), y))
    then_.assign(x, rest(x))
    else_.assign(x, stack(top(y), x))
    else_.assign(y, rest(y))

    m.assert_invariant("negated_goal", y != the_tower)

    expected = """
        module blockworld {
            var x: datatype tower = {stack(top: enum {S, D, F, G}, rest: this) | empty};
            var y: datatype tower = {stack(top: enum {S, D, F, G}, rest: this) | empty};
            var choice: boolean;
            init {
                x = stack(S, stack(D, stack(F, stack(G, empty))));
                y = empty;
            }
            next {
                havoc choice';
                if (choice) {
                    y' = stack(x.top, y);
                    x' = x.rest;
                } else {
                    x' = stack(y.top, x);
                    y' = y.rest;
                }
            }
            invariant negated_goal: y != stack(S, stack(D, stack(F, stack(G, empty))));
        }
    """

    assert str(m).split() == expected.split()
