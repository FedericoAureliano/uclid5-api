from importlib.metadata import PackageNotFoundError, version  # pragma: no cover

try:
    # Change here if project is renamed and does not equal the package name
    dist_name = "uclid5-api"
    __version__ = version(dist_name)
except PackageNotFoundError:  # pragma: no cover
    __version__ = "unknown"
finally:
    del version, PackageNotFoundError

import z3

from .expr import prime
from .module import Module
from .printer import UCLIDFormatter
from .types import array, bitvector, boolean, integer, real
from .verify import bmc, induction

z3.z3printer._Formatter = UCLIDFormatter()

__all__ = [
    "Module",
    "integer",
    "real",
    "boolean",
    "array",
    "bitvector",
    "prime",
    "bmc",
    "induction",
]
