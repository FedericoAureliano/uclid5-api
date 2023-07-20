# uclid5-api

## Installing
```sh
pip3 install . # use -e flag when developing
```

## Usage Example
The following Python code
```python
from uclid5_api import Module, induction, integer

m = Module("fib")
a = m.declare_var("a", integer())
b = m.declare_var("b", integer())
m.init.assign(a, 0)
m.init.assign(b, 1)
m.next.assign(a, b)
m.next.assign(b, a + b)
m.assert_invariant("b_gte_0", b >= 0)

print(m)
```

will print
```
module fib {
  var a: integer;
  var b: integer;
  init {
    a = 0;
    b = 1;
  }
  next {
    a' = b;
    b' = a + b;
  }
  invariant b_gte_0: b >= 0;
}
```

## Testing
```sh
pipx run tox
```

## Formatting
```sh
pipx run pre-commit run --all-files --show-diff-on-failure
```

## Verification (*EXPERIMENTAL*)
You can attempt a proof-by-induction with the `induction` function.

```python
m = Module("test")
x = m.declare_var("x", integer())

m.init.assign(x, 0)
then_, else_ = m.init.branch(x == 0)
then_.assign(x, x + 1)
else_.assign(x, x + 2)
m.init.assign(x, x * 7)

m.assert_invariant("x_eq_7", x == 7)
assert induction(m) is True
```

You can generate the SMT-LIB queries by giving the induction function a file name prefix, e.g., `induction(m, "test")`.
