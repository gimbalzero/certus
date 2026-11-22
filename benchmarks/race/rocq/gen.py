#!/usr/bin/env python3
"""N copies of the sum theorem in Rocq. Usage: python3 gen.py N [Module] > Module.v"""

import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
from copies import generate  # noqa: E402

generate(os.path.join(HERE, "Sum.v"), "(* COPY *)", "(* END COPY *)", {'sumTo': 'sumTo{i}', 'sum_formula': 't{i}'}, header=None)
