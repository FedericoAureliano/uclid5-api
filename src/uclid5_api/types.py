import z3


def sort(name):
    """
    Return an uninterpreted sort
    """
    return z3.DeclareSort(name)


def integer():
    """
    Return the integer sort
    """
    return z3.IntSort()


integer_sort = integer
IntegerSort = integer


def boolean():
    """
    Return the integer sort
    """
    return z3.BoolSort()


boolean_sort = boolean
BooleanSort = boolean
BoolSort = boolean
bool_sort = boolean


def real():
    """
    Return the real sort
    """
    return z3.RealSort()


real_sort = real
RealSort = real


def array(index, elem):
    """
    Return the array sort
    """
    return z3.ArraySort(index, elem)


array_sort = array
ArraySort = array


def bitvector(size):
    """
    Return the bitvector sort
    """
    return z3.BitVecSort(size)


bitvector_sort = bitvector
BitVecSort = bitvector
bv_sort = bitvector
BVSort = bitvector


def enum(*args):
    """
    Return the enum sort
    """
    variants = list(args)
    name = "Enum_" + "_".join(variants)
    t, vs = z3.EnumSort(name, variants)
    return t, vs


def record(*args):
    """
    Return the record sort
    """
    field_names = [n for (n, _) in args]
    field_types = [t for (_, t) in args]
    name = "Record_" + "_".join(field_names)
    dt = z3.Datatype(name)
    dt.declare(name, *[(n, t) for (n, t) in zip(field_names, field_types)])
    t = dt.create()
    return t, t.constructor(0), [t.accessor(0, i) for i in range(len(field_names))]


def datatype(name, *constructors):
    """
    Return the datatype sort
    """
    dt = z3.Datatype(name)
    for c, args in constructors:
        sels = []
        for n, t in args:
            if isinstance(t, str) and t == this():
                sels.append((n, dt))
            else:
                sels.append((n, t))
        dt.declare(c, *sels)
    t = dt.create()
    return (
        t,
        [t.constructor(i) for i in range(len(constructors))],
        [
            t.accessor(i, j)
            for i in range(len(constructors))
            for j in range(len(constructors[i][1]))
        ],
        [t.recognizer(i) for i in range(len(constructors))],
    )


def this():
    return "this"
