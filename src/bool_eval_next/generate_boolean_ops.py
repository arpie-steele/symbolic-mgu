#!/usr/bin/env python3
"""
Generate BooleanSimpleOp enum with human-readable names.

This script exhaustively searches for short, meaningful names for all 278
Boolean operations by composing basic operations.

The algorithm:
1. Start with promoted operations (lower arity operations used at higher arity)
2. Try compositions of basic operations (And, Or, Not, Xor, etc.) on
   permutations of inputs
3. Try If-then-else structures
4. For remaining operations, generate descriptive fallback names

Total operations: 278 = 2 + 4 + 16 + 256
- Nullary: 2 (codes 0x00, 0xff)
- Unary: 4 (codes 0x00, 0x55, 0xaa, 0xff)
- Binary: 16 (codes 0x00, 0x11, 0x22, ..., 0xff)
- Ternary: 256 (codes 0x00 through 0xff)
"""

from typing import Dict, List, Tuple, Optional, Set
from dataclasses import dataclass
from ast import parse, Expression

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

    def generate_all(self) -> Dict[Tuple[int, int], BooleanOp]:
        """Generate all 278 Boolean operations."""
        self._add_nullary()
        self._add_unary()
        self._add_binary()
        self._add_ternary()

        return self.ops

    def _add_nullary(self):
        """Add nullary operations (2 total)."""
        self.add_op(0, 0x00, "False0", "false", "Constant false.")
        self.add_op(0, 0xff, "True0", "true", "Constant true.")

    def _add_unary(self):
        """Add unary operations (4 total)."""
        # Basic unary
        self.add_op(1, 0x55, "NotA1", "!a", "Logical negation.")
        self.add_op(1, 0xaa, "IdA1", "a", "Identity function.")

        # Promoted from nullary
        self.add_op(1, 0x00, "False1", "false",
                    "Constant false. See `False0`.",
                    promoted_from=(0, "False0"))
        self.add_op(1, 0xff, "True1", "true",
                    "Constant true. See `True0`.",
                    promoted_from=(0, "True0"))

    def _add_binary(self):
        """Add binary operations (16 total)."""
        # Basic binary operations
        binary_ops = [
            (0x11, "NotOrAB2", "Nor(a, b)", "NOR", ["NorAB2"]),
            (0x22, "NotImpliesAB2", "NotImplies(a, b)",
             "Inhibition (A and not B)", []),
            (0x33, "NotB2", "~b", "Negation of b. See `NotA1`.", []),
            (0x44, "NotImpliesBA2", "NotImplies(b, a)",
             "Inhibition (B and not A)", []),
            (0x55, "NotA2", "~a", "Negation of a. See `NotA1`.", []),
            (0x66, "XorAB2", "Xor(a, b)", "Exclusive OR", ["ExclusiveOrAB2"]),
            (0x77, "NotAndAB2", "Nand(a, b)", "NAND", ["NandAB2"]),
            (0x88, "AndAB2", "And(a, b)", "Logical AND", []),
            (0x99, "NotXorAB2", "Biimp(a, b)",
             "Logical equivalence (XNOR)", ["BiimpAB2", "EqAB2"]),
            (0xaa, "IdA2", "a", "Identity on a. See `IdA1`.", []),
            (0xbb, "ImpliesBA2", "Implies(b, a)",
             "Reverse implication (B implies A)", ["RevImpliesAB2"]),
            (0xcc, "IdB2", "b", "Identity on b.", []),
            (0xdd, "ImpliesAB2", "Implies(a, b)",
             "Material implication (A implies B)", []),
            (0xee, "OrAB2", "Or(a, b)", "Logical OR", []),
        ]

        for code, name, expr, comment, aliases in binary_ops:
            self.add_op(2, code, name, expr, comment, aliases)

        # Promoted from nullary/unary
        self.add_op(2, 0x00, "False2", "false",
                    "Constant false. See `False0`.",
                    promoted_from=(0, "False0"))
        self.add_op(2, 0xff, "True2", "true",
                    "Constant true. See `True0`.",
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
        # Promote binary operations (ignore c)
        for code in get_valid_codes(2):
            if code in [0x00, 0xff]:  # Skip constants, handled separately
                continue
            # Find the binary operation name
            binary_op = self.ops.get((2, code))
            if binary_op and not binary_op.promoted_from:
                # This is a "real" binary operation, promote it
                base_name = binary_op.name[:-1]  # Remove the "2"
                new_name = f"{base_name}3"
                self.add_op(3, code, new_name, binary_op.expr,
                            f"Binary operation on a and b, ignoring c."
                            f" See `{binary_op.name}`.",
                            promoted_from=(2, binary_op.name))

        # Promote unary operations (ignore b and c)
        for code in get_valid_codes(1):
            if code in [0x00, 0xff]:  # Skip constants
                continue
            unary_op = self.ops.get((1, code))
            if unary_op and not unary_op.promoted_from:
                base_name = unary_op.name[:-1]  # Remove the "1"
                new_name = f"{base_name}3"
                self.add_op(3, code, new_name, unary_op.expr,
                            f"Unary operation on a, ignoring b and c."
                            f" See `{unary_op.name}`.",
                            promoted_from=(1, unary_op.name))

        # Promote nullary operations
        self.add_op(3, 0x00, "False3", "false",
                    "Constant false. See `False0`.",
                    promoted_from=(0, "False0"))
        self.add_op(3, 0xff, "True3", "true",
                    "Constant true. See `True0`.",
                    promoted_from=(0, "True0"))

        # Add operations on b and c (promoted identity/negation patterns)
        self.add_op(3, 0xcc, "IdB3", "b", "Identity on b.")
        self.add_op(3, 0x33, "NotB3", "!b", "Negation of b.")
        self.add_op(3, 0xf0, "IdC3", "c", "Identity on c.")
        self.add_op(3, 0x0f, "NotC3", "!c", "Negation of c.")

    def _add_basic_ternary(self):
        """Add well-known ternary operations."""

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
            ]
        for var2 in ["c"]:
            for (pythonic_expr, comment) in [
                (var2, "Identity function on {var2}."),
                (f"~{var2}", "Negation of {var2}.")
            ]:
                ast: Expression = parse(pythonic_expr, mode='eval')
                code = code_from_ints(ast)
                name = name_from_strs(ast) + "3"
                rust_expr = rust_from_strs(ast)
                self.add_op(3, code, name, rust_expr, comment, [])
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
                    ast = parse(pythonic_expr, mode='eval')
                    code = code_from_ints(ast)
                    name = name_from_strs(ast) + "3"
                    rust_expr = rust_from_strs(ast)
                    self.add_op(3, code, name, rust_expr, comment, [])

        for (pythonic_expr, comment) in simples:
            ast = parse(pythonic_expr, mode='eval')
            code = code_from_ints(ast)
            name = name_from_strs(ast) + "3"
            rust_expr = rust_from_strs(ast)
            self.add_op(3, code, name, rust_expr, comment, [])

        ternary_ops = [
            (0x80, "AndABC3", "And3(a, b, c)", "Three-way AND", ["And3"]),
            (0xfe, "OrABC3", "Or3(a, b, c)", "Three-way OR", ["Or3"]),
            (0x96, "XorABC3", "Xor3(a, b, c)",
             "Three-way XOR (odd parity)", ["Xor3", "ParityABC3"]),
            (0xe8, "MajorityABC3", "Majority(a, b, c)",
             "Majority function (at least 2 of 3 true)",
             ["Majority3", "CarryABC3"]),
            (0xd8, "IfABC3", "b if a else c",
             "If a then b else c (multiplexer)", ["MuxABC3"]),
            (0x7f, "NotAndABC3", "NotAnd3(a, b, c)",
             "Three-way NAND", ["Nand3"]),
            (0x01, "NotOrABC3", "NotOr3(a, b, c)",
             "Three-way NOR", ["Nor3"]),
            (0x69, "NotXorABC3", "NotXor3(a, b, c)",
             "Three-way XNOR (even parity)", []),
        ]

        for code, name, expr, comment, aliases in ternary_ops:
            self.add_op(3, code, name, expr, comment, aliases)

        # Add variations of If-then-else (all 6 permutations of a, b, c)
        if_variations = [
            (0xd8, "IfABC3", "b if a else c", "If a then b else c"),
            (0xe4, "IfACB3", "c if a else b", "If a then c else b"),
            (0xb8, "IfBAC3", "a if b else c", "If b then a else c"),
            (0xe2, "IfBCA3", "c if b else a", "If b then c else a"),
            (0xca, "IfCAB3", "a if c else b", "If c then a else b"),
            (0xd4, "IfCBA3", "b if c else a", "If c then b else a"),
        ]

        for code, name, expr, comment in if_variations:
            if code not in self.named_at_arity[3]:
                self.add_op(3, code, name, expr, comment)

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
        "EnumDiscriminants",
        "EnumString",
        "FromRepr",
        "VariantArray",
        "VariantNames"
        ])

    # Generate header
    header = f'''//! Generated Boolean operations enum.
//!
//! This file is AUTO-GENERATED by generate_boolean_ops.py
//! Do not edit manually!

use strum::{{
    {strum_parts},
}};

/// All {total} Boolean operations on 0-3 variables.
///
/// Total operations: 278 = 2^(2^0) + 2^(2^1) + 2^(2^2) + 2^(2^3)
///
/// Discriminant encoding: `0xN_CC` where:
/// - `N` = arity (0, 1, 2, or 3)
/// - `CC` = truth table with inputs a=0xaa, b=0xcc, c=0xf0
///
/// Count by arity:
/// - Nullary: {counts[0]} operations (2^(2^0) = 2)
/// - Unary: {counts[1]} operations (2^(2^1) = 4)
/// - Binary: {counts[2]} operations (2^(2^2) = 16)
/// - Ternary: {counts[3]} operations (2^(2^3) = 256)
#[derive(
    Clone,
    Copy,
    Debug,
    PartialEq,
    Eq,
    Hash,
    Display,
    EnumCount,
    EnumDiscriminants,
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
    impl_block = '''
}

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

    # Documentation comment
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
    variant = f"    {op.name} = {op.format_discriminant()},"
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

    output_file = "enum.rs"
    with open(output_file, "w",  encoding="utf-8") as f:
        f.write(rust_code)

    print(f"\nGenerated {output_file}")


if __name__ == "__main__":
    main()
