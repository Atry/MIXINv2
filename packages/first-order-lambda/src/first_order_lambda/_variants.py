"""The reading callback and the two readings of the (single-valued) shape.

``Sh`` is single-valued, so there is no aggregate over a set; a reading just maps the
stabilized shape to a head decision for the readout. The only freedom is at ``EMPTY`` (an
unproductive cycle): the operational reading ``Sbot`` renders it as bottom, the
least-fixpoint reading ``Semp`` renders it as the empty constructor ``lambda a. lambda b.
b``. A concrete shape reads out to itself, so the readings agree on the pure fragment
(conservativity).
"""

from __future__ import annotations

from enum import Enum, auto
from typing import Callable

from first_order_lambda._ast import ShapeBottom
from first_order_lambda._shape import Shape


class Resolution(Enum):
    """Non-shape readout decisions."""

    BOTTOM = auto()
    """Divergence leaf, written bottom."""

    EMPTY_CONSTRUCTOR = auto()
    """The second Scott constructor ``lambda a. lambda b. b``, the empty cycle's readout."""


ReadResult = Shape | Resolution

Reading = Callable[[Shape | ShapeBottom], ReadResult]


def operational(shape: Shape | ShapeBottom) -> ReadResult:
    """``Sbot``: a stabilized empty cycle reads out as bottom."""
    if shape is ShapeBottom.EMPTY:
        return Resolution.BOTTOM
    return shape


def least_model(shape: Shape | ShapeBottom) -> ReadResult:
    """``Semp``: a stabilized empty cycle reads out as the empty constructor."""
    if shape is ShapeBottom.EMPTY:
        return Resolution.EMPTY_CONSTRUCTOR
    return shape
