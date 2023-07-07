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

You can also use bmc and induction. For example, adding
```
bmc(m, 5)
```
to the previous code will print
```
No counterexample found after unrolling 5 times!
```
and
```
induction(m)
```
will print
```
Found a counterexample at the inductive step for invariant b_gte_0!
  Before next:
    a := -1
    b := 0
  After next:
    a := -1
    b := 0
```

## Testing
```sh
pipx run tox
```
