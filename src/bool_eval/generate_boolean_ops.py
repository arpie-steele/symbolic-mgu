#!/usr/bin/env python3
"""
Generate BooleanSimpleOp enum with human-readable names.

This script exhaustively searches for short, meaningful names for all 278
Boolean operations by composing basic operations.

The idea for an algorithm:
1. Start with promoted operations (lower arity operations used at higher arity)
2. Try compositions of basic operations (And, Or, Not, Xor, etc.) on
   permutations of inputs
3. Try If-then-else structures
4. For remaining operations, generate descriptive fallback names

Actually, we just tried some things by hand, taking into account
the symmetry of the functions, and curated a list of things to try.
First one to fill the missing slot wins.

Total operations: 278 = 2 + 4 + 16 + 256
- Nullary: 2 (codes 0x00, 0xff)
- Unary: 4 (codes 0x00, 0x55, 0xaa, 0xff)
- Binary: 16 (codes 0x00, 0x11, 0x22, ..., 0xff)
- Ternary: 256 (codes 0x00 through 0xff)
"""

from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass
from ast import parse, Expression
import inspect

# mypy: check-untyped-defs

# Import our AST expression parser
from ast_expr_parse import (EvalUint, code_from_ints, name_from_strs,
                            rust_from_strs)


# Truth table constants for a, b, c
TT_A = 0xaa  # 10101010
TT_B = 0xcc  # 11001100
TT_C = 0xf0  # 11110000


@dataclass
class BooleanOp:
    """Represents a boolean operation with its properties."""
    arity: int
    code: int
    name: str
    expr: str
    comment: str
    aliases: List[str]
    promoted_from: Optional[Tuple[int, str]] = None

    @property
    def discriminant(self) -> int:
        """
        Compute Rust enum discriminant from this operation's arity and code.
        """
        return (self.arity << 8) | self.code

    def format_discriminant(self) -> str:
        """
        Format the Rust enum discriminant in a way that emphasizes its
        structure.
        """
        if self.code == 0x16 or self.code == 0x32 or self.code == 0x64:
            return f"0x{self.arity:x}{self.code:02x}"
        return f"0x{self.arity:x}_{self.code:02x}"


def eval_expr(expr: str, a: int = TT_A, b: int = TT_B,
              c: int = TT_C) -> Optional[int]:
    """Evaluate a Rust-like boolean expression and return truth table.

    Uses ast_expr_parse.py's EvalUint engine for proper AST-based evaluation.
    """
    try:
        # Parse the expression
        ast_expr: Expression = parse(expr, mode='eval')

        # Evaluate using the integer engine
        eng = EvalUint()
        result = eng.eval(ast_expr, {
            "a": a,
            "b": b,
            "c": c,
            "True": 0xff,
            "False": 0x00
        })
        return result & 0xff
    except (ValueError, SyntaxError) as msg:
        print(f"Error evaluating expr='{expr}': {msg}")
        return None


def todo() -> str:
    """Generate a TODO comment with line number for cross-referencing.

    Uses stack frame introspection to automatically determine the line number
    where this function was called.
    """
    frame = inspect.currentframe()
    if frame is not None and frame.f_back is not None:
        line_number = frame.f_back.f_lineno
        return f"TODO at line={line_number}."
    return "TODO"


def get_valid_codes(arity: int) -> List[int]:
    """Get all valid truth table codes for given arity."""
    num_bits = 1 << arity  # 2^arity bits needed
    max_code = 1 << num_bits  # 2^(2^arity) possible codes

    if arity == 0:
        # Nullary: only 2 operations (constant false/true)
        return [0xff * i for i in range(max_code)]
    elif arity == 1:
        # Unary: 4 operations on 2 bits
        # 00, 01, 10, 11 -> but extended to byte: 00, 55, aa, ff
        return [0x55 * i for i in range(max_code)]
    elif arity == 2:
        # Binary: 16 operations on 4 bits
        return [0x11 * i for i in range(max_code)]
    elif arity == 3:
        # Ternary: all 256 operations
        return [i for i in range(max_code)]

    return []


class NameGenerator:
    """Generates human-readable names for Boolean operations."""

    def __init__(self):
        self.ops: Dict[Tuple[int, int], BooleanOp] = {}
        self.named_at_arity: Dict[int, Set[int]] = {
            0: set(),
            1: set(),
            2: set(),
            3: set()
            }

    def add_op(self, arity: int, code: int, name: str, expr: str,
               comment: str = "", aliases: Optional[List[str]] = None,
               promoted_from: Optional[Tuple[int, str]] = None) -> bool:
        """Add an operation if not already named."""
        if code in self.named_at_arity[arity]:
            return False

        self.ops[(arity, code)] = BooleanOp(
            arity=arity,
            code=code,
            name=name,
            expr=expr,
            comment=comment,
            aliases=aliases or [],
            promoted_from=promoted_from
        )
        self.named_at_arity[arity].add(code)
        return True

    def add_computed_op(self,
                        arity: int,
                        pythonic_expr: str,
                        comment: str = "",
                        aliases: Optional[List[str]] = None,
                        promoted_from: Optional[Tuple[int, str]] = None
                        ) -> bool:
        """Add an operation if not already named."""
        ast: Expression = parse(pythonic_expr, mode="eval")
        code = code_from_ints(ast)
        name = name_from_strs(ast) + str(arity)
        rust_expr = rust_from_strs(ast)
        return self.add_op(arity, code, name, rust_expr,
                           comment, aliases, promoted_from)

    def generate_all(self) -> Dict[Tuple[int, int], BooleanOp]:
        """Generate all 278 Boolean operations."""
        self._add_nullary()
        self._add_unary()
        self._add_binary()
        self._add_ternary()

        return self.ops

    def _add_nullary(self):
        """Add nullary operations (2 total)."""
        self.add_computed_op(0, "False", "Constant false.")
        self.add_computed_op(0, "True", "Constant true.")

    def _add_unary(self):
        """Add unary operations (4 total)."""
        # Basic unary
        self.add_computed_op(1, "~a",
                             "Logical negation on first (only) variable.")
        self.add_computed_op(1, "a",
                             "Identity function on first (only) variable.")

        # Promoted from nullary
        self.add_computed_op(1, "False", "Constant false. See `False0`.",
                             promoted_from=(0, "False0"))
        self.add_computed_op(1, "True", "Constant true. See `True0`.",
                             promoted_from=(0, "True0"))

    def _add_binary(self):
        """Add binary operations (16 total)."""
        # Basic binary operations
        self.add_computed_op(2, "NotOr(a, b)",
                             "NOR operator on first two variables.")
        self.add_computed_op(2, "NotImplies(a, b)",
                             "Not(a implies b). Inhibition, And(a, not b).",
                             ['AndANotB2'])
        self.add_computed_op(2, "~b",
                             "Logical negation on second variable."
                             " See `NotA1`.")
        self.add_computed_op(2, "NotImplies(b, a)",
                             "Not(b implies a). Inhibition, And(not a, b).",
                             ['AndNotAB2'])
        self.add_computed_op(2, "Xor(a, b)",
                             "Logical XOR (Exclusive Or) operator"
                             " on first two variables.",
                             ["ExclusiveOrAB2"])
        self.add_computed_op(2, "NotAnd(a, b)",
                             "Logical NAND operator on first two variables.",
                             ["NandAB2"])
        self.add_computed_op(2, "And(a, b)",
                             "Logical AND operator on first two variables.")
        self.add_computed_op(2, "Biimp(a, b)",
                             "Logical equivalence (XNOR) operator"
                             " on first two variables.",
                             ["BiimpAB2", "EqAB2", "NotXorAB2"])
        self.add_computed_op(2, "Implies(b, a)",
                             "Reverse implication (B implies A).",
                             ["OrANotB2"])
        self.add_computed_op(2, "b", "Identity on second variable.")
        self.add_computed_op(2, "Implies(a, b)",
                             "Material implication (A implies B).",
                             ["OrNotAB2"])
        self.add_computed_op(2, "Or(a, b)",
                             "Logical OR (Exclusive Or) operator"
                             " on first two variables.")

        # Promoted from unary

        self.add_computed_op(2, "~a",
                             "Logical negation on first variable.",
                             promoted_from=(1, "NotA1"))
        self.add_computed_op(2, "a",
                             "Identity on first variable.",
                             promoted_from=(1, "IdA1"))

        # Promoted from nullary

        self.add_computed_op(2, "False", "Constant false. See `False0`.",
                             promoted_from=(0, "False0"))
        self.add_computed_op(2, "True", "Constant true. See `True0`.",
                             promoted_from=(0, "True0"))

    def _add_ternary(self):
        """Add ternary operations (256 total)."""
        # First, promote all lower-arity operations
        self._promote_to_ternary()

        # Add basic ternary operations
        self._add_basic_ternary()

        # Try to name remaining operations through composition
        self._name_by_composition()

        # Fill in any remaining with descriptive fallback names
        self._add_fallback_ternary()

    def _promote_to_ternary(self):
        """Promote nullary, unary, and binary operations to ternary."""

        # Promoted from binary
        self.add_computed_op(3, "NotOr(a, b)",
                             "NOR operator on first two variables.",
                             promoted_from=(2, "NotOrAB2"))
        self.add_computed_op(3, "NotImplies(a, b)",
                             "Not(a implies b). Inhibition, And(a, not b).",
                             ['AndANotB3'], promoted_from=(2, "NotImpliesAB2"))
        self.add_computed_op(3, "~b",
                             "Logical negation on second variable."
                             " See `NotA1`.", promoted_from=(2, "NotB2"))
        self.add_computed_op(3, "NotImplies(b, a)",
                             "Not(b implies a). Inhibition, And(not a, b).",
                             ['AndNotAB2'], promoted_from=(2, "NotImpliesBA2"))
        self.add_computed_op(3, "Xor(a, b)",
                             "Logical XOR (Exclusive Or) operator"
                             " on first two variables.",
                             ["ExclusiveOrAB2"], promoted_from=(2, "XorAB2"))
        self.add_computed_op(3, "NotAnd(a, b)",
                             "Logical NAND operator on first two variables.",
                             ["NandAB2"], promoted_from=(2, "NotAndAB2"))
        self.add_computed_op(3, "And(a, b)",
                             "Logical AND operator on first two variables.",
                             promoted_from=(2, "AndAB2"))
        self.add_computed_op(3, "Biimp(a, b)",
                             "Logical equivalence (XNOR) operator"
                             " on first two variables.",
                             ["BiimpAB2", "EqAB2", "NotXorAB2"],
                             promoted_from=(2, "NotXorAB2"))
        self.add_computed_op(3, "Implies(b, a)",
                             "Reverse implication (B implies A).",
                             ["OrANotB2"], promoted_from=(2, "ImpliesBA2"))
        self.add_computed_op(3, "b", "Identity on second variable.",
                             promoted_from=(2, "IdB2"))
        self.add_computed_op(3, "Implies(a, b)",
                             "Material implication (A implies B).",
                             ["OrNotAB2"], promoted_from=(2, "ImpliesAB2"))
        self.add_computed_op(3, "Or(a, b)",
                             "Logical OR (Exclusive Or) operator"
                             " on first two variables.",
                             promoted_from=(2, "OrAB2"))

        # Promoted from unary

        self.add_computed_op(3, "~a",
                             "Logical negation on first variable.",
                             promoted_from=(1, "NotA1"))
        self.add_computed_op(3, "a",
                             "Identity on first variable.",
                             promoted_from=(1, "IdA1"))

        # Promoted from nullary

        self.add_computed_op(3, "False", "Constant false. See `False0`.",
                             promoted_from=(0, "False0"))
        self.add_computed_op(3, "True", "Constant true. See `True0`.",
                             promoted_from=(0, "True0"))

    def _add_basic_ternary(self):
        """Add well-known ternary operations."""
        # Promoted binary operators where at `c` is referenced
        for var2 in ["c"]:
            for (pythonic_expr, comment) in [
                (var2, f"Identity function on {var2}."),
                (f"~{var2}", f"Negation of {var2}.")
            ]:
                self.add_computed_op(3, pythonic_expr, comment)
            for var1 in ["a", "b"]:
                for (pythonic_expr, comment) in [
                    (f"NotAnd({var1}, {var2})", f"Nand({var1}, {var2})."),
                    (f"And({var1}, {var2})", f"And({var1}, {var2})."),
                    (f"NotOr({var1}, {var2})", f"Nor({var1}, {var2})."),
                    (f"Or({var1}, {var2})", f"Or({var1}, {var2})."),
                    (f"Xor({var1}, {var2})", f"Xor({var1}, {var2})."),
                    (f"NotXor({var1}, {var2})", f"Biimp({var1}, {var2})."),
                    (f"NotImplies({var1}, {var2})",
                     f"Not(Implies({var1}, {var2}))."),
                    (f"NotImplies({var2}, {var1})",
                     f"Not(Implies({var2}, {var1}))."),
                    (f"Implies({var1}, {var2})", f"Implies({var1}, {var2})."),
                    (f"Implies({var2}, {var1})", f"Implies({var2}, {var1})."),
                ]:
                    self.add_computed_op(3, pythonic_expr, comment)

        # Ternary operators, symmetric on all three inputs
        self.add_computed_op(3, "And3(a, b, c)", "Three-way AND operator.")
        self.add_computed_op(3, "Or3(a, b, c)", "Three-way OR operator.")
        self.add_computed_op(3, "Xor3(a, b, c)",
                             "Three-way XOR operator (odd parity).")
        self.add_computed_op(3, "Majority(a, b, c)",
                             "Majority function (at least 2 of 3 true).",
                             ["CarryABC3"])
        self.add_computed_op(3, "NotAnd3(a, b, c)", "Three-way NAND operator.")
        self.add_computed_op(3, "NotOr3(a, b, c)", "Three-way NOR operator.")
        self.add_computed_op(3, "NotXor3(a, b, c)",
                             "Three-way XNOR operator (even parity).")
        self.add_computed_op(3, "NotMajority(a, b, c)",
                             "Minority function (at least 2 of 3 false).",
                             ["NotCarryABC3"])
        # More Complicated Symmetry
        self.add_computed_op(3, "b if a else c",
                             "If a then b else c (multiplexer).", ["MuxABC3"])
        self.add_computed_op(3, "c if a else b",
                             "If a then c else b (multiplexer).", ["MuxACB3"])
        self.add_computed_op(3, "a if b else c",
                             "If b then a else c (multiplexer).", ["MuxBAC3"])
        self.add_computed_op(3, "c if b else a",
                             "If b then c else a (multiplexer).", ["MuxBCA3"])
        self.add_computed_op(3, "a if c else b",
                             "If c then a else b (multiplexer).", ["MuxCAB3"])
        self.add_computed_op(3, "b if c else a",
                             "If c then b else a (multiplexer).", ["MuxCBA3"])
        self.add_computed_op(3, "~(b if a else c)",
                             "If a then not b else not c"
                             " (negated multiplexer).", ["NotMuxABC3"])
        self.add_computed_op(3, "~(c if a else b)",
                             "If a then not c else not b"
                             " (negated multiplexer).", ["NotMuxACB3"])
        self.add_computed_op(3, "~(a if b else c)",
                             "If b then not a else not c"
                             " (negated multiplexer).", ["NotMuxBAC3"])
        self.add_computed_op(3, "~(c if b else a)",
                             "If b then not c else not a"
                             " (negated multiplexer).", ["NotMuxBCA3"])
        self.add_computed_op(3, "~(a if c else b)",
                             "If c then not a else not b"
                             " (negated multiplexer).", ["NotMuxCAB3"])
        self.add_computed_op(3, "~(b if c else a)",
                             "If c then not b else not a"
                             " (negated multiplexer).", ["NotMuxCBA3"])

        self.add_computed_op(3, "~b if a else c",
                             "If a then not b else c"
                             " (multiplexer, negated input).", ["MuxANotBC3"])
        self.add_computed_op(3, "~c if a else b",
                             "If a then not c else b"
                             " (multiplexer, negated input).", ["MuxANotCB3"])
        self.add_computed_op(3, "~a if b else c",
                             "If b then not a else c"
                             " (multiplexer, negated input).", ["MuxBNotAC3"])
        self.add_computed_op(3, "~c if b else a",
                             "If b then not c else a"
                             " (multiplexer, negated input).", ["MuxBNotCA3"])
        self.add_computed_op(3, "~a if c else b",
                             "If c then not a else b"
                             " (multiplexer, negated input).", ["MuxCNotAB3"])
        self.add_computed_op(3, "~b if c else a",
                             "If c then not b else a"
                             " (multiplexer, negated input).", ["MuxCNotBA3"])

        self.add_computed_op(3, "b if a else ~c",
                             "If a then b else not c"
                             " (multiplexer, negated input).", ["MuxABNotC3"])
        self.add_computed_op(3, "c if a else ~b",
                             "If a then c else not b"
                             " (multiplexer, negated input).", ["MuxACNotB3"])
        self.add_computed_op(3, "a if b else ~c",
                             "If b then a else not c"
                             " (multiplexer, negated input).", ["MuxBANotC3"])
        self.add_computed_op(3, "c if b else ~a",
                             "If b then c else not a"
                             " (multiplexer, negated input).", ["MuxBCNotA3"])
        self.add_computed_op(3, "a if c else ~b",
                             "If c then a else not b"
                             " (multiplexer, negated input).", ["MuxCANotB3"])
        self.add_computed_op(3, "b if c else ~a",
                             "If c then b else not a"
                             " (multiplexer, negated input).", ["MuxCBNotA3"])

        simples = [
            ('And3(a, b, c)', "True only when all of a, b, and c are."),
            ('And3(~a, b, c)', "True only when all of not a, b, and c are."),
            ('And3(a, ~b, c)', "True only when all of a, not b, and c are."),
            ('And3(a, b, ~c)', "True only when all of a, b, and not c are."),
            ('NotOr3(~a, b, c)',
             "True only when all of a, not b, and not c are."),
            ('NotOr3(a, ~b, c)',
             "True only when all of not a, b, and not c are."),
            ('NotOr3(a, b, ~c)',
             "True only when all of not a, not b, and c are."),
            ('NotOr3(a, b, c)',
             "True only when all of not a, not b, and not c are."),
            ('Or3(a, b, c)', "False only when all of a, b, and c are."),
            ('Or3(~a, b, c)', "False only when all of not a, b, and c are."),
            ('Or3(a, ~b, c)', "False only when all of a, not b, and c are."),
            ('Or3(a, b, ~c)', "False only when all of a, b, and not c are."),
            ('NotAnd3(~a, b, c)',
             "False only when all of a, not b, and not c are."),
            ('NotAnd3(a, ~b, c)',
             "False only when all of not a, b, and not c are."),
            ('NotAnd3(a, b, ~c)',
             "False only when all of not a, not b, and c are."),
            ('NotAnd3(a, b, c)',
             "False only when all of not a, not b, and not c are."),
            ('If(a, b, c)', "If a then b else c."),
            ('If(a, c, b)', "If a then c else b."),
            ('If(b, a, c)', "If b then a else c."),
            ('If(b, c, a)', "If b then c else a."),
            ('If(c, a, b)', "If c then a else b."),
            ('If(c, b, a)', "If c then b else a."),

            ('If(a, ~b, c)', "If a then not b else c."),
            ('If(a, ~c, b)', "If a then not c else b."),
            ('If(b, ~a, c)', "If b then not a else c."),
            ('If(b, ~c, a)', "If b then not c else a."),
            ('If(c, ~a, b)', "If c then not a else b."),
            ('If(c, ~b, a)', "If c then not b else a."),

            ('If(a, b, ~c)', "If a then b else not c."),
            ('If(a, c, ~b)', "If a then c else not b."),
            ('If(b, a, ~c)', "If b then a else not c."),
            ('If(b, c, ~a)', "If b then c else not a."),
            ('If(c, a, ~b)', "If c then a else not b."),
            ('If(c, b, ~a)', "If c then b else not a."),

            ('NotIf(a, b, c)', "If a then not b else not c."),
            ('NotIf(a, c, b)', "If a then not c else not b."),
            ('NotIf(b, a, c)', "If b then not a else not c."),
            ('NotIf(b, c, a)', "If b then not c else not a."),
            ('NotIf(c, a, b)', "If c then not a else not b."),
            ('NotIf(c, b, a)', "If c then not b else not a."),

            ('Implies(Xor(a, b), c)', "Xor(a, b) implies c."),
            ('Implies(Or(a, b), c)', "Or(a, b) implies c."),
            ('Implies(And(a, b), c)', "And(a, b) implies c."),
            ('Or(Xor(a, b), c)', "Biimp(a, b) implies c."),
            ('Or(Or(a, b), c)', "NotOr(a, b) implies c."),
            ('Or(And(a, b), c)', "NotAnd(a, b) implies c."),

            ('Implies(Xor(a, c), b)', "Xor(a, c) implies b."),
            ('Implies(Or(a, c), b)', "Or(a, c) implies b."),
            ('Implies(And(a, c), b)', "And(a, c) implies b."),
            ('Or(Xor(a, c), b)', "Biimp(a, c) implies b."),
            ('Or(Or(a, c), b)', "NotOr(a, c) implies b."),
            ('Or(And(a, c), b)', "NotAnd(a, c) implies b."),

            ('Implies(Xor(b, c), a)', "Xor(b, c) implies a."),
            ('Implies(Or(b, c), a)', "Or(b, c) implies a."),
            ('Implies(And(b, c), a)', "And(b, c) implies a."),
            ('Or(Xor(b, c), a)', "Biimp(b, c) implies a."),
            ('Or(Or(b, c), a)', "NotOr(b, c) implies a."),
            ('Or(And(b, c), a)', "NotAnd(b, c) implies a."),

            ('Implies(Xor(a, b), ~c)', "Xor(a, b) implies not c."),
            ('Implies(Or(a, b), ~c)', "Or(a, b) implies not c."),
            ('Implies(And(a, b), ~c)', "And(a, b) implies not c."),
            ('Implies(c, Xor(a, b))', "c implies Xor(a, b)."),
            ('Implies(c, Or(a, b))', "c implies Or(a, b)."),
            ('Implies(c, And(a, b))', "c implies And(a, b)."),

            ('Implies(Xor(a, c), ~b)', "Xor(a, c) implies not b."),
            ('Implies(Or(a, c), ~b)', "Or(a, c) implies not b."),
            ('Implies(And(a, c), ~b)', "And(a, c) implies not b."),
            ('Implies(b, Xor(a, c))', "b implies Xor(a, c)."),
            ('Implies(b, Or(a, c))', "b implies Or(a, c)."),
            ('Implies(b, And(a, c))', "b implies And(a, c)."),

            ('Implies(Xor(b, c), ~a)', "Xor(b, c) implies not a."),
            ('Implies(Or(b, c), ~a)', "Or(b, c) implies not a."),
            ('Implies(And(b, c), ~a)', "And(b, c) implies not a."),
            ('Implies(a, Xor(b, c))', "a implies Xor(b, c)."),
            ('Implies(a, Or(b, c))', "a implies Or(b, c)."),
            ('Implies(a, And(b, c))', "a implies And(b, c)."),

            ('Implies(Implies(a, b), c)', 'Implies(Implies(a, b), c)'),
            ('Implies(Implies(a, c), b)', 'Implies(Implies(a, c), b)'),
            ('Implies(Implies(b, a), c)', 'Implies(Implies(b, a), c)'),
            ('Implies(Implies(b, c), a)', 'Implies(Implies(b, c), a)'),
            ('Implies(Implies(c, a), b)', 'Implies(Implies(c, a), b)'),
            ('Implies(Implies(c, b), a)', 'Implies(Implies(c, b), a)'),

            ('Implies(Implies(a, b), ~c)', 'Implies(Implies(a, b), not c)'),
            ('Implies(Implies(a, c), ~b)', 'Implies(Implies(a, c), not b)'),
            ('Implies(Implies(b, a), ~c)', 'Implies(Implies(b, a), not c)'),
            ('Implies(Implies(b, c), ~a)', 'Implies(Implies(b, c), not a)'),
            ('Implies(Implies(c, a), ~b)', 'Implies(Implies(c, a), not b)'),
            ('Implies(Implies(c, b), ~a)', 'Implies(Implies(c, b), not a)'),

            ('~a & (b | c)', 'And(not a, Or(b, c))'),
            ('~b & (a | c)', 'And(not b, Or(a, c))'),
            ('~c & (a | b)', 'And(not c, Or(a, b))'),
            ('a & (b | c)', 'And(a, Or(b, c))'),
            ('b & (a | c)', 'And(b, Or(a, c))'),
            ('c & (a | b)', 'And(c, Or(a, b))'),

            ('~a & (~b | c)', 'And(not a, Or(not b, c))'),
            ('~b & (~a | c)', 'And(not b, Or(not a, c))'),
            ('~c & (~a | b)', 'And(not c, Or(not a, b))'),
            ('a & (~b | c)', 'And(a, Or(not b, c))'),
            ('b & (~a | c)', 'And(b, Or(not a, c))'),
            ('c & (~a | b)', 'And(c, Or(not a, b))'),

            ('~a & (b | ~c)', 'And(not a, Or(b, not c))'),
            ('~b & (a | ~c)', 'And(not b, Or(a, not c))'),
            ('~c & (a | ~b)', 'And(not c, Or(a, not b))'),
            ('a & (b | ~c)', 'And(a, Or(b, not c))'),
            ('b & (a | ~c)', 'And(b, Or(a, not c))'),
            ('c & (a | ~b)', 'And(c, Or(a, not b))'),

            ('~a & (b ^ c)', 'And(not a, Xor(b, c))'),
            ('~b & (a ^ c)', 'And(not b, Xor(a, c))'),
            ('~c & (a ^ b)', 'And(not c, Xor(a, b))'),
            ('a & (b ^ c)', 'And(a, Xor(b, c))'),
            ('b & (a ^ c)', 'And(b, Xor(a, c))'),
            ('c & (a ^ b)', 'And(c, Xor(a, b))'),

            ('~a & (b ^ c)', 'And(not a, NotXor(b, c))'),
            ('~b & (a ^ c)', 'And(not b, NotXor(a, c))'),
            ('~c & (a ^ b)', 'And(not c, NotXor(a, b))'),
            ('a & (b ^ c)', 'And(a, NotXor(b, c))'),
            ('b & (a ^ c)', 'And(b, NotXor(a, c))'),
            ('c & (a ^ b)', 'And(c, NotXor(a, b))'),
            ('NotOr(a, Xor(b, c))', 'not Or(a, Xor(b, c))'),
            ('NotOr(b, Xor(a, c))', 'not Or(a, Xor(b, c))'),
            ('NotOr(c, Xor(a, b))', 'not Or(a, Xor(b, c))'),

            ('Or(a, And(b, c))', 'Or(a, And(b, c))'),
            ('Or(b, And(a, c))', 'Or(b, And(a, c))'),
            ('Or(c, And(a, b))', 'Or(c, And(a, b))'),
            ('Or(~a, And(b, c))', 'Or(not a, And(b, c))'),
            ('Or(~b, And(a, c))', 'Or(not b, And(a, c))'),
            ('Or(~c, And(a, b))', 'Or(not c, And(a, b))'),

            ('Or(a, And(~b, c))', 'Or(a, And(not b, c))'),
            ('Or(b, And(~a, c))', 'Or(b, And(not a, c))'),
            ('Or(c, And(~a, b))', 'Or(c, And(not a, b))'),
            ('Or(~a, And(~b, c))', 'Or(not a, And(not b, c))'),
            ('Or(~b, And(~a, c))', 'Or(not b, And(not a, c))'),
            ('Or(~c, And(~a, b))', 'Or(not c, And(not a, b))'),

            ('Or(a, And(b, ~c))', 'Or(a, And(b, not c))'),
            ('Or(b, And(a, ~c))', 'Or(b, And(a, not c))'),
            ('Or(c, And(a, ~b))', 'Or(c, And(a, not b))'),
            ('Or(~a, And(b, ~c))', 'Or(not a, And(b, not c))'),
            ('Or(~b, And(a, ~c))', 'Or(not b, And(a, not c))'),
            ('Or(~c, And(a, ~b))', 'Or(not c, And(a, not b))'),

            ('NotOr(a, And(b, c))', 'NotOr(a, And(b, c))'),
            ('NotOr(b, And(a, c))', 'NotOr(b, And(a, c))'),
            ('NotOr(c, And(a, b))', 'NotOr(c, And(a, b))'),
            ('NotOr(~a, And(b, c))', 'NotOr(not a, And(b, c))'),
            ('NotOr(~b, And(a, c))', 'NotOr(not b, And(a, c))'),
            ('NotOr(~c, And(a, b))', 'NotOr(not c, And(a, b))'),

            ('NotOr(a, And(~b, c))', 'NotOr(a, And(not b, c))'),
            ('NotOr(b, And(~a, c))', 'NotOr(b, And(not a, c))'),
            ('NotOr(c, And(~a, b))', 'NotOr(c, And(not a, b))'),
            ('NotOr(~a, And(~b, c))', 'NotOr(not a, And(not b, c))'),
            ('NotOr(~b, And(~a, c))', 'NotOr(not b, And(not a, c))'),
            ('NotOr(~c, And(~a, b))', 'NotOr(not c, And(not a, b))'),

            ('NotOr(a, And(b, ~c))', 'NotOr(a, And(b, not c))'),
            ('NotOr(b, And(a, ~c))', 'NotOr(b, And(a, not c))'),
            ('NotOr(c, And(a, ~b))', 'NotOr(c, And(a, not b))'),
            ('NotOr(~a, And(b, ~c))', 'NotOr(not a, And(b, not c))'),
            ('NotOr(~b, And(a, ~c))', 'NotOr(not b, And(a, not c))'),
            ('NotOr(~c, And(a, ~b))', 'NotOr(not c, And(a, not b))'),

            ('Majority(a, b, c)',
             'Majority function (true when least 2 of a, b, c are true)'),
            ('NotMajority(a, b, c)',
             'Minority function (true when least 2 of a, b, c are false)'),
            ('Majority(~a, b, c)',
             'Majority function (true when least 2 of not a, b, c are true)'),
            ('NotMajority(~a, b, c)',
             'Minority function (true when least 2 of not a, b, c are false)'),
            ('Majority(a, ~b, c)',
             'Majority function (true when least 2 of a, not b, c are true)'),
            ('NotMajority(a, ~b, c)',
             'Minority function (true when least 2 of a, not b, c are false)'),
            ('Majority(a, b, ~c)',
             'Majority function (true when least 2 of a, b, not c are true)'),
            ('NotMajority(a, b, ~c)',
             'Minority function (true when least 2 of a, b, not c are false)'),

            ('NotOr(a & b, Xor3(a, b, c))', 'Even parity (0 or 2 inputs), but not when both a and b are true'),
            ('NotOr(a & c, Xor3(a, b, c))', 'Even parity (0 or 2 inputs), but not when both a and c are true'),
            ('NotOr(b & c, Xor3(a, b, c))', 'Even parity (0 or 2 inputs), but not when both b and c are true'),

            ('NotOr(NotOr(a, b), Xor3(a, b, c))', 'At least one of a or b, and even parity of all three'),

            ('NotOr(a & b, NotXor3(a, b, c))', 'Exactly one of the three inputs is true'),
            ('NotOr(~a & b, NotXor3(a, b, c))', 'Odd parity (1 or 3 inputs), but not when it is just b that is true'),
            ('NotOr(~a & c, NotXor3(a, b, c))', 'Odd parity (1 or 3 inputs), but not when it is just c that is true'),
            ('NotOr(a & ~b, NotXor3(a, b, c))', 'Odd parity (1 or 3 inputs), but not when it is just a that is true'),

            ('Xor(a, b) & Xor(a, c)', 'Variable a differs from both b and c (so b equals c)'),
            ('Xor(a, b) | Xor(a, c)', 'Variable a differs from b or from c (not all three equal)'),
            ('Xor(a, b) & NotXor(a, c)', 'Variable a differs from b but equals c (so b differs from c)'),
            ('Xor(a, b) | NotXor(a, c)', 'Variable a differs from b, or a equals c'),
            ('NotXor(a, b) & Xor(a, c)', 'Variable a equals b but differs from c (so b differs from c)'),
            ('NotXor(a, b) | Xor(a, c)', 'Variable a equals b, or a differs from c'),
            ('NotOr(Xor(a, b), Xor(a, c))', 'All three variables are equal (neither parity holds)'),
            ('NotAnd(Xor(a, b), Xor(a, c))', 'Variable a equals at least one of b or c'),

            ('And(Xor(a, b), Or(a, c))', 'Exactly one of a or b is true, while at least one of a or c'),
            ('And(Xor(a, b), Or(b, c))', 'Exactly one of a or b is true, while at least one of b or c'),
            ('And(Xor(a, c), Or(a, b))', 'Exactly one of a or c is true, while at least one of a or b'),
            ('And(Xor(a, c), Or(b, c))', 'Exactly one of a or c is true, while at least one of b or c'),
            ('And(Xor(b, c), Or(a, b))', 'Exactly one of b or c is true, while at least one of a or b'),
            ('And(Xor(b, c), Or(a, c))', 'Exactly one of b or c is true, while at least one of a or c'),

            ('And(NotXor(a, b), Or(a, c))', 'Variables a and b are equal, while at least one of a or c'),
            ('And(NotXor(a, c), Or(a, b))', 'Variables a and c are equal, while at least one of a or b'),
            ('And(NotXor(b, c), Or(a, b))', 'Variables b and c are equal, while at least one of a or b'),

            ('Or(Xor(a, b), And(a, c))', 'Either a differs from b, or both a and c are true'),
            ('Or(Xor(a, c), And(a, b))', 'Either a differs from c, or both a and b are true'),
            ('Or(Xor(b, c), And(a, b))', 'Either b differs from c, or both a and b are true'),

            ('Or(NotXor(a, b), And(a, c))', 'Either a equals b, or both a and c are true'),
            ('Or(NotXor(a, b), And(b, c))', 'Either a equals b, or both b and c are true'),
            ('Or(NotXor(a, c), And(a, b))', 'Either a equals c, or both a and b are true'),
            ('Or(NotXor(a, c), And(b, c))', 'Either a equals c, or both b and c are true'),
            ('Or(NotXor(b, c), And(a, b))', 'Either b equals c, or both a and b are true'),
            ('Or(NotXor(b, c), And(a, c))', 'Either b equals c, or both a and c are true'),

            ('NotAnd(Xor(a, b), Or(a, c))', 'Either a equals b, or neither a nor c is true'),
            ('NotAnd(Xor(a, b), Or(b, c))', 'Either a equals b, or neither b nor c is true'),
            ('NotAnd(Xor(a, c), Or(a, b))', 'Either a equals c, or neither a nor b is true'),
            ('NotAnd(Xor(a, c), Or(b, c))', 'Either a equals c, or neither b nor c is true'),
            ('NotAnd(Xor(b, c), Or(a, b))', 'Either b equals c, or neither a nor b is true'),
            ('NotAnd(Xor(b, c), Or(a, c))', 'Either b equals c, or neither a nor c is true'),

            ('NotAnd(NotXor(a, b), Or(a, c))', 'Either a differs from b, or neither a nor c is true'),
            ('NotAnd(NotXor(a, c), Or(a, b))', 'Either a differs from c, or neither a nor b is true'),
            ('NotAnd(NotXor(b, c), Or(a, b))', 'Either b differs from c, or neither a nor b is true'),

            ('NotOr(Xor(a, b), And(a, c))', 'Variable a equals b, and not both a and c'),
            ('NotOr(Xor(a, c), And(a, b))', 'Variable a equals c, and not both a and b'),
            ('NotOr(Xor(b, c), And(a, b))', 'Variable b equals c, and not both a and b'),

            ('NotOr(NotXor(a, b), And(a, c))', 'Variable a differs from b, and not both a and c'),
            ('NotOr(NotXor(a, b), And(b, c))', 'Variable a differs from b, and not both b and c'),
            ('NotOr(NotXor(a, c), And(a, b))', 'Variable a differs from c, and not both a and b'),
            ('NotOr(NotXor(a, c), And(b, c))', 'Variable a differs from c, and not both b and c'),
            ('NotOr(NotXor(b, c), And(a, b))', 'Variable b differs from c, and not both a and b'),
            ('NotOr(NotXor(b, c), And(a, c))', 'Variable b differs from c, and not both a and c'),

            ('Xor(a, Or(b, c))', 'Variable a differs from the disjunction of b and c'),
            ('NotXor(a, Or(b, c))', 'Variable a equals the disjunction of b and c'),
            ('Xor(a, And(b, c))', 'Variable a differs from the conjunction of b and c'),
            ('NotXor(a, And(b, c))', 'Variable a equals the conjunction of b and c'),
            ('Xor(a, Or(~b, c))', 'Variable a differs from (b implies c)'),
            ('NotXor(a, Or(~b, c))', 'Variable a equals (b implies c)'),
            ('Xor(a, And(~b, c))', 'Variable a differs from both not-b and c'),
            ('NotXor(a, And(~b, c))', 'Variable a equals (not-b and c)'),

            ('Xor(b, Or(a, c))', 'Variable b differs from the disjunction of a and c'),
            ('NotXor(b, Or(a, c))', 'Variable b equals the disjunction of a and c'),
            ('Xor(b, And(a, c))', 'Variable b differs from the conjunction of a and c'),
            ('NotXor(b, And(a, c))', 'Variable b equals the conjunction of a and c'),
            ('Xor(b, Or(~a, c))', 'Variable b differs from (a implies c)'),
            ('NotXor(b, Or(~a, c))', 'Variable b equals (a implies c)'),
            ('Xor(b, And(~a, c))', 'Variable b differs from both not-a and c'),
            ('NotXor(b, And(~a, c))', 'Variable b equals (not-a and c)'),

            ('Xor(c, Or(a, b))', 'Variable c differs from the disjunction of a and b'),
            ('NotXor(c, Or(a, b))', 'Variable c equals the disjunction of a and b'),
            ('Xor(c, And(a, b))', 'Variable c differs from the conjunction of a and b'),
            ('NotXor(c, And(a, b))', 'Variable c equals the conjunction of a and b'),
            ('Xor(c, Or(~a, b))', 'Variable c differs from (a implies b)'),
            ('NotXor(c, Or(~a, b))', 'Variable c equals (a implies b)'),
            ('Xor(c, And(~a, b))', 'Variable c differs from both not-a and b'),
            ('NotXor(c, And(~a, b))', 'Variable c equals (not-a and b)'),

            ('Or(Xor(a, b), And(~a, c))', 'Either a differs from b, or both not-a and c are true'),
            ('Or(Xor(a, c), And(~a, b))', 'Either a differs from c, or both not-a and b are true'),

            ('Or(Xor(c, b), And(~c, a))', 'Either c differs from b, or both not-c and a are true'),

            ('Or(Xor(a, b), And(a, ~c))', 'Either a differs from b, or both a and not-c are true'),
            ('Or(Xor(a, c), And(a, ~b))', 'Either a differs from c, or both a and not-b are true'),

            ('Or(Xor(c, b), And(c, ~a))', 'Either c differs from b, or both c and not-a are true'),

            ('Or(Xor3(a, b, c), And(a, b))', 'Either odd parity of all three, or both a and b are true'),
            ('Or(Xor3(a, b, c), And(a, c))', 'Either odd parity of all three, or both a and c are true'),
            ('Or(Xor3(a, b, c), And(b, c))', 'Either odd parity of all three, or both b and c are true'),
            ('Or(NotXor3(a, b, c), And(a, b))', 'Either even parity of all three, or both a and b are true'),

            ('Or(NotXor3(a, b, c), And(~a, b))', 'Either even parity of all three, or both not-a and b are true'),
            ('Or(NotXor3(a, b, c), And(~a, c))', 'Either even parity of all three, or both not-a and c are true'),

            ('Or(NotXor3(a, b, c), And(a, ~b))', 'Either even parity of all three, or both a and not-b are true'),

            ('Or(Xor3(a, b, c), NotOr(a, b))',
             'True iff zero or an odd number of a, b, and c are true.'),

            ('And(NotXor(a, b), Or(~a, c))',
             'True iff a == b and a == ( b and c ).'),
            ('And(NotXor(a, b), Or(a, ~c))',
             'True iff a == b and a == ( b or c ).'),

            ('And(NotXor(a, c), Or(~a, b))',
             'True iff a == c and a == ( b and c ).'),
            ('And(NotXor(a, c), Or(a, ~b))',
             'True iff a == c and a == ( b or c ).'),

            ('And(NotXor(b, c), Or(~a, b))',
             'True iff b == c and b == ( a or c ).'),
            ('And(NotXor(b, c), Or(a, ~b))',
             'True iff b == c and b == ( a and c ).'),

            ('And(a, NotXor(b, c))', 'True iff a is true and b == c.'),
            ('And(b, NotXor(a, c))', 'True iff b is true and a == c.'),
            ('And(c, NotXor(a, b))', 'True iff c is true and a == b.'),

            ]

        for (pythonic_expr, comment) in simples:
            self.add_computed_op(3, pythonic_expr, comment)

    def _name_by_composition(self):
        """Try to name remaining operations by composition."""
        # This is where we'd do exhaustive search for compositions
        # For now, we'll add some common patterns

        # Operations involving And/Or of pairs
        compositions = [
            # (a & b) | c variations
            (0xf8, "OrCAB3", "And(a, b) | c", "c OR (a AND b)"),
            (0xea, "OrCBA3", "And(b, a) | c",
             "c OR (b AND a)"),  # Same as above

            # (a | b) & c variations
            (0xe0, "AndCAB3", "Or(a, b) & c", "c AND (a OR b)"),

            # Negated versions
            (0x07, "NotOrCAB3", "~(And(a, b) | c)", "NOT(c OR (a AND b))"),
            (0x1f, "NotAndCAB3", "~(Or(a, b) & c)", "NOT(c AND (a OR b))"),
        ]

        for code, name, expr, comment in compositions:
            if code not in self.named_at_arity[3]:
                code_check = eval_expr(expr)
                if code_check == code:
                    self.add_op(3, code, name, expr, comment)

    def _add_fallback_ternary(self):
        """Add descriptive fallback names for any remaining operations."""
        for code in range(256):
            if code in self.named_at_arity[3]:
                continue

            # Generate descriptive name based on the pattern
            name = self._generate_descriptive_name(code)
            expr = self._generate_canonical_expr(code)
            comment = f"Complex Boolean operation 0x{code:02x}."

            self.add_op(3, code, name, expr, comment)

    def _generate_descriptive_name(self, code: int) -> str:
        """Generate a descriptive name for a truth table code."""
        # Analyze the truth table to find a pattern
        bits = format(code, '08b')

        # Count ones
        ones = bits.count('1')

        if ones == 1:
            # Exactly one true case - find it
            pos = 7 - bits.index('1')
            return f"OnlyTrue{pos:03b}3"
        elif ones == 7:
            # Exactly one false case
            pos = 7 - bits.index('0')
            return f"OnlyFalse{pos:03b}3"
        else:
            # General case - just use the hex code
            return f"ABCOp{code:02X}Todo3"

    def _generate_canonical_expr(self, code: int) -> str:
        """Generate a canonical expression from truth table."""
        # This generates DNF (disjunctive normal form)
        terms = []
        for i in range(8):
            if (code >> i) & 1:
                # This minterm is true
                a_val = (i >> 0) & 1
                b_val = (i >> 1) & 1
                c_val = (i >> 2) & 1

                term_parts = []
                if a_val:
                    term_parts.append("a")
                else:
                    term_parts.append("!a")
                if b_val:
                    term_parts.append("b")
                else:
                    term_parts.append("!b")
                if c_val:
                    term_parts.append("c")
                else:
                    term_parts.append("!c")

                terms.append(f"({' & '.join(term_parts)})")

        if not terms:
            return "false"
        elif len(terms) == 8:
            return "true"
        else:
            return " | ".join(terms)


def generate_rust_enum(ops: Dict[Tuple[int, int], BooleanOp]) -> str:
    """Generate complete Rust enum definition."""
    # Sort operations by discriminant
    sorted_ops = sorted(ops.values(), key=lambda op: op.discriminant)

    # Count operations
    counts = {0: 0, 1: 0, 2: 0, 3: 0}
    for op in sorted_ops:
        counts[op.arity] += 1

    total = sum(counts.values())

    strum_parts = ", ".join([
        "Display",
        "EnumCount",
        "EnumString",
        "FromRepr",
        "VariantArray",
        "VariantNames"
        ])

    # Generate header
    header = f'''//! Generated Boolean operations enum.
//!
//! This file is AUTO-GENERATED by `generate_boolean_ops.py`
//! Do not edit manually!
#![allow(missing_docs)]

use strum::{{{strum_parts}}};

/// All {total} Boolean operations on 0-3 variables.
///
/// Total operations: 278 = `2^(2^0)` + `2^(2^1)` + `2^(2^2)` + `2^(2^3)`
///
/// Discriminant encoding: `0xN_CC` where:
/// - `N` = arity (0, 1, 2, or 3)
/// - `CC` = truth table with inputs a=0xaa, b=0xcc, c=0xf0
///
/// Count by arity:
/// - Nullary: {counts[0]} operations (`2^(2^0)` = 2)
/// - Unary: {counts[1]} operations (`2^(2^1)` = 4)
/// - Binary: {counts[2]} operations (`2^(2^2)` = 16)
/// - Ternary: {counts[3]} operations (`2^(2^3)` = 256)
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
    Display,
    EnumCount,
    EnumString,
    FromRepr,
    VariantArray,
    VariantNames,
)]
#[repr(u16)]
pub enum BooleanSimpleOp {{
'''

    # Generate variants
    variants = []
    for op in sorted_ops:
        variants.append(_format_variant(op))

    # Generate impl block
    impl_block = '''}

impl BooleanSimpleOp {
    /// Get the arity of the operator.
    #[inline]
    pub fn get_arity(&self) -> u8 {
        ((*self as u16 >> 8) & 0x3) as u8
    }

    /// Get the truth table of the operator as if it applied to 3 variables.
    ///
    /// This is compatible with Mathematica's
    /// `BooleanFunction[code3, {a, b, c}]`.
    ///
    /// The reduced truth table is
    /// `code_n = (code3 >> 0) & ((1 << (1 << n)) - 1)`
    /// where `n` is the arity.
    #[inline]
    pub fn get_code3(&self) -> u8 {
        (*self as u16 & 0xff) as u8
    }
}
'''

    return header + "\n".join(variants) + "\n" + impl_block


def _format_variant(op: BooleanOp) -> str:
    """Format a single enum variant with documentation."""
    lines = []

    # Documentation comment - append op name in backticks if TODO
    if op.comment.startswith("TODO"):
        lines.append(f"    /// {op.comment} `{op.name}`")
    else:
        lines.append(f"    /// {op.comment}")

    if op.expr:
        lines.append("    ///")
        lines.append(f"    /// Expression: `{op.expr}`")

    if op.promoted_from:
        lower_arity, simpler = op.promoted_from
        lines.append("    ///")
        lines.append(
            f"    /// Note: Promoted from `{simpler}` (arity {lower_arity})."
            )

    if op.aliases:
        lines.append("    ///")
        alias_str = ", ".join(f"`{a}`" for a in op.aliases)
        lines.append(f"    /// Aliases: {alias_str}")

    # Variant definition
    props = f"    #[strum(props(Expr = \"{op.expr}\"))]"
    variant = f"    {op.name} = {op.format_discriminant()},"
    lines.append(props)
    lines.append(variant)

    return "\n".join(lines)


def main():
    """Generate the enum.rs file."""
    print("Generating Boolean operations...")

    gen = NameGenerator()
    ops = gen.generate_all()

    print(f"\nGenerated {len(ops)} operations:")
    for arity in range(4):
        count = sum(1 for op in ops.values() if op.arity == arity)
        expected = 2 ** (2 ** arity)
        status = "✓" if count == expected else "✗"
        print(f"  {status} Arity {arity}: {count}/{expected} operations")

    rust_code = generate_rust_enum(ops)

    output_file = "generated_enum.rs"
    with open(output_file, "w",  encoding="utf-8") as f:
        f.write(rust_code)

    print(f"\nGenerated {output_file}")


if __name__ == "__main__":
    main()
