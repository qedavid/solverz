"""Compare my level-2 results (open.log) with x_ma_iterated.out per (row, p, H'' invariant factors)."""
import re, sys
from collections import defaultdict, Counter
sys.path.insert(0, ".")
from exists_c36 import inv_factors  # noqa (module runs nothing on import? guard below)
