#!/usr/bin/env python3
"""
Test parse of boolean expressions.
"""

from sys import version as sys_version
from ast import parse, dump, AST, Expression
from inspect import currentframe, getframeinfo
from typing import TypeVar, Generic


T = TypeVar("T")


class EvalEngine(Generic[T]):
    """Related classes to evaluate an expression."""
    def eval_not(self, node: AST, values: dict[str, T]) -> T:
        """Evalute Not1 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_not()")

    def eval_and(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute And2 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_and()")

    def eval_or(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute Or2 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_or()")

    def eval_xor(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute Xor2 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_xor()")

    def eval_imp(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute Implies expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_imp()")

    def eval_nand(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute NotAnd2 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nand()")

    def eval_nor(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute NotOr2 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nor()")

    def eval_nxor(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute NotXor2 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nxor()")

    def eval_nimp(self, left: AST, right: AST, values: dict[str, T]) -> T:
        """Evalute NotImplies2 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nimp()")

    def eval_and3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute And3 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_and3()")

    def eval_nand3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute NotAnd3 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nand3()")

    def eval_or3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute Or3 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_or3()")

    def eval_nor3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute NotOr3 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nor3()")

    def eval_xor3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute Xor3 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_xor3()")

    def eval_nxor3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute NotXor3 expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nxor3()")

    def eval_maj3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute Majority expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_maj3()")

    def eval_nmaj3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute NotMajority expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nmaj3()")

    def eval_if3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute If expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_if3()")

    def eval_nif3(self, a: AST, b: AST, c: AST, values: dict[str, T]) -> T:
        """Evalute NotIf expression."""
        raise NotImplementedError(f"{type(self).__name__}.eval_nif3()")

    def eval(self, node: AST, values: dict[str, T]) -> T:
        """Evaluate expression."""
        node_type = type(node).__name__
        if node_type == "Expression":
            body = getattr(node, "body")
            return self.eval(body, values)
        if node_type == "Name":
            var_id = getattr(node, "id")
            ctx = getattr(node, "ctx")
            if type(ctx).__name__ != "Load":
                raise ValueError(f"Expected ctx={ctx} to be Load "
                                 f"for {dump(node)}")
            if var_id in values:
                return values[var_id]
            raise ValueError(f"Expected id={var_id} to be one of "
                             f"{','.join(values.keys())} for {dump(node)}")
        if node_type == "Constant":
            value = getattr(node, "value")
            value_type = type(value).__name__
            if value_type == "bool":
                return values["True"] if value else values["False"]
            raise ValueError(f"Expected value={value}:{value_type} "
                             f"to be one of "
                             f"[True, False]:bool for {dump(node)} "
                             f"on {sys_version}")
        if node_type == "UnaryOp":
            op = getattr(node, "op")
            operand = getattr(node, "operand")
            op_type = type(op).__name__
            if op_type == "Invert":
                return self.eval_not(operand, values)
            raise ValueError(f"Expected op={dump(op)} to be "
                             f"Invert() for {dump(node)}")
        if node_type == "IfExp":
            if_test = getattr(node, "test")
            body = getattr(node, "body")
            orelse = getattr(node, "orelse")
            return self.eval_if3(if_test, body, orelse, values)
        if node_type == "BinOp":
            left = getattr(node, "left")
            op = getattr(node, "op")
            op_type = type(op).__name__
            right = getattr(node, "right")
            if op_type == "BitAnd":
                return self.eval_and(left, right, values)
            if op_type == "BitOr":
                return self.eval_or(left, right, values)
            if op_type == "BitXor":
                return self.eval_xor(left, right, values)
            raise ValueError(f"Expected op={dump(op)} to be "
                             f"one of BitAnd*(),BitOr(),BitXor() "
                             f"for {dump(node)}")
        if node_type == "Call":
            func = getattr(node, "func")
            func_type = type(func).__name__
            if func_type != "Name":
                raise ValueError(f"Expected func.type={func_type} to be "
                                 f"Name for {dump(node)}")
            func_id = getattr(func, "id")
            func_ctx = getattr(func, "ctx")
            if type(func_ctx).__name__ != "Load":
                raise ValueError(f"Expected ctx={func_ctx} "
                                 f"to be Load for {dump(node)}")
            args = getattr(node, "args")
            if func_id == "Not":
                if len(args) != 1:
                    raise ValueError(f"Expected exactly 1 arg "
                                     f"for {func_id} in {dump(node)}")
                return self.eval_not(args[0], values)
            if func_id in ["Implies", "And", "Or", "Xor", "Biimp", "Nor",
                           "Nand", "NotImplies", "NotAnd", "NotXor",
                           "NotOr"]:
                if len(args) != 2:
                    raise ValueError(f"Expected exactly 2 args for "
                                     f"{func_id} in {dump(node)}")
                if func_id == "Implies":
                    return self.eval_imp(args[0], args[1], values)
                elif func_id == "And":
                    return self.eval_and(args[0], args[1], values)
                elif func_id == "Or":
                    return self.eval_or(args[0], args[1], values)
                elif func_id == "Xor":
                    return self.eval_xor(args[0], args[1], values)
                elif func_id == "Biimp" or func_id == "NotXor":
                    return self.eval_nxor(args[0], args[1], values)
                elif func_id == "Nor" or func_id == "NotOr":
                    return self.eval_nor(args[0], args[1], values)
                elif func_id == "Nand" or func_id == "NotAnd":
                    return self.eval_nand(args[0], args[1], values)
                elif func_id == "NotImplies":
                    return self.eval_nimp(args[0], args[1], values)
            if func_id in ["And3", "Or3", "Xor3", "NotOr3", "NotXor3",
                           "NotAnd3", "Majority", "NotMajority", "If",
                           "NotIf"]:
                if len(args) != 3:
                    raise ValueError(f"Expected exactly 3 args "
                                     f"for {func_id} in {dump(node)}")
                if func_id == "And3":
                    return self.eval_and3(args[0], args[1], args[2], values)
                elif func_id == "Or3":
                    return self.eval_or3(args[0], args[1], args[2], values)
                elif func_id == "Xor3":
                    return self.eval_xor3(args[0], args[1], args[2], values)
                elif func_id == "Majority":
                    return self.eval_maj3(args[0], args[1], args[2], values)
                elif func_id == "NotMajority":
                    return self.eval_nmaj3(args[0], args[1], args[2], values)
                elif func_id == "NotXor3":
                    return self.eval_nxor3(args[0], args[1], args[2], values)
                elif func_id == "NotOr3":
                    return self.eval_nor3(args[0], args[1], args[2], values)
                elif func_id == "NotAnd3":
                    return self.eval_nand3(args[0], args[1], args[2], values)
                elif func_id == "If":
                    return self.eval_if3(args[0], args[1], args[2], values)
                elif func_id == "NotIf":
                    return self.eval_nif3(args[0], args[1], args[2], values)
            raise ValueError(f"Expected func.id={func_id} to be one of "
                             f"Not,Implies,And,Or,Xor,Biimp,Nor,Nand,"
                             f"NotImplies,And3,Or3,Xor3,NotAnd3,NotOr3,"
                             f"NotXor3,If,NotIf "
                             f"for {func_id} in {dump(node)}")

        raise ValueError(f"Expected different syntax: {dump(node)}")


class EvalBool(EvalEngine[bool]):
    """A class to evaluate an expression."""

    def eval_not(self, node: AST, values: dict[str, bool]) -> bool:
        return not self.eval(node, values)

    def eval_and(self, left: AST, right: AST, values: dict[str, bool]) -> bool:
        return self.eval(left, values) and self.eval(right, values)

    def eval_or(self, left: AST, right: AST, values: dict[str, bool]) -> bool:
        return self.eval(left, values) or self.eval(right, values)

    def eval_xor(self, left: AST, right: AST, values: dict[str, bool]) -> bool:
        return self.eval(left, values) ^ self.eval(right, values)

    def eval_imp(self, left: AST, right: AST, values: dict[str, bool]) -> bool:
        return not self.eval(left, values) or self.eval(right, values)

    def eval_nand(self, left: AST, right: AST,
                  values: dict[str, bool]) -> bool:
        return not (self.eval(left, values) and self.eval(right, values))

    def eval_nor(self, left: AST, right: AST, values: dict[str, bool]) -> bool:
        return not (self.eval(left, values) or self.eval(right, values))

    def eval_nxor(self, left: AST, right: AST,
                  values: dict[str, bool]) -> bool:
        return not self.eval(left, values) ^ self.eval(right, values)

    def eval_nimp(self, left: AST, right: AST,
                  values: dict[str, bool]) -> bool:
        return self.eval(left, values) and not self.eval(right, values)

    def eval_and3(self, a: AST, b: AST, c: AST,
                  values: dict[str, bool]) -> bool:
        return (self.eval(a, values)
                and self.eval(b, values)
                and self.eval(c, values))

    def eval_nand3(self, a: AST, b: AST, c: AST,
                   values: dict[str, bool]) -> bool:
        return not (self.eval(a, values)
                    and self.eval(b, values)
                    and self.eval(c, values))

    def eval_or3(self, a: AST, b: AST, c: AST,
                 values: dict[str, bool]) -> bool:
        return (self.eval(a, values)
                or self.eval(b, values)
                or self.eval(c, values))

    def eval_nor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, bool]) -> bool:
        return not (self.eval(a, values)
                    or self.eval(b, values)
                    or self.eval(c, values))

    def eval_xor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, bool]) -> bool:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return a_v ^ b_v ^ c_v

    def eval_nxor3(self, a: AST, b: AST, c: AST,
                   values: dict[str, bool]) -> bool:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return not a_v ^ b_v ^ c_v

    def eval_maj3(self, a: AST, b: AST, c: AST,
                  values: dict[str, bool]) -> bool:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return (a_v and b_v or a_v and c_v or b_v and c_v)

    def eval_nmaj3(self, a: AST, b: AST, c: AST,
                   values: dict[str, bool]) -> bool:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return not (a_v and b_v or a_v and c_v or b_v and c_v)

    def eval_if3(self, a: AST, b: AST, c: AST,
                 values: dict[str, bool]) -> bool:
        return (self.eval(b, values)
                if self.eval(a, values)
                else self.eval(c, values))

    def eval_nif3(self, a: AST, b: AST, c: AST,
                  values: dict[str, bool]) -> bool:
        return (not self.eval(b, values)
                if self.eval(a, values)
                else not self.eval(c, values))


class EvalUint(EvalEngine[int]):
    """A class to evaluate an expression."""

    def eval_not(self, node: AST, values: dict[str, int]) -> int:
        return values["True"] ^ self.eval(node, values)

    def eval_and(self, left: AST, right: AST, values: dict[str, int]) -> int:
        return self.eval(left, values) & self.eval(right, values)

    def eval_or(self, left: AST, right: AST, values: dict[str, int]) -> int:
        return self.eval(left, values) | self.eval(right, values)

    def eval_xor(self, left: AST, right: AST, values: dict[str, int]) -> int:
        return self.eval(left, values) ^ self.eval(right, values)

    def eval_imp(self, left: AST, right: AST, values: dict[str, int]) -> int:
        return ((values["True"]
                 ^ self.eval(left, values))
                | self.eval(right, values))

    def eval_nand(self, left: AST, right: AST,
                  values: dict[str, int]) -> int:
        return ((self.eval(left, values)
                 & self.eval(right, values))
                ^ values["True"])

    def eval_nor(self, left: AST, right: AST, values: dict[str, int]) -> int:
        return ((self.eval(left, values)
                 | self.eval(right, values))
                ^ values["True"])

    def eval_nxor(self, left: AST, right: AST,
                  values: dict[str, int]) -> int:
        return (values["True"]
                ^ self.eval(left, values)
                ^ self.eval(right, values))

    def eval_nimp(self, left: AST, right: AST,
                  values: dict[str, int]) -> int:
        return (self.eval(left, values)
                & (values["True"]
                   ^ self.eval(right, values)))

    def eval_and3(self, a: AST, b: AST, c: AST,
                  values: dict[str, int]) -> int:
        return (self.eval(a, values)
                & self.eval(b, values)
                & self.eval(c, values))

    def eval_nand3(self, a: AST, b: AST, c: AST,
                   values: dict[str, int]) -> int:
        return ((self.eval(a, values)
                 & self.eval(b, values)
                 & self.eval(c, values))
                ^ values["True"])

    def eval_or3(self, a: AST, b: AST, c: AST,
                 values: dict[str, int]) -> int:
        return (self.eval(a, values)
                | self.eval(b, values)
                | self.eval(c, values))

    def eval_nor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, int]) -> int:
        return ((self.eval(a, values)
                 | self.eval(b, values)
                 | self.eval(c, values))
                ^ values["True"])

    def eval_xor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, int]) -> int:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return a_v ^ b_v ^ c_v

    def eval_nxor3(self, a: AST, b: AST, c: AST,
                   values: dict[str, int]) -> int:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return values["True"] ^ a_v ^ b_v ^ c_v

    def eval_maj3(self, a: AST, b: AST, c: AST,
                  values: dict[str, int]) -> int:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return a_v & b_v | a_v & c_v | b_v & c_v

    def eval_nmaj3(self, a: AST, b: AST, c: AST,
                   values: dict[str, int]) -> int:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return ((a_v & b_v | a_v & c_v | b_v & c_v)
                ^ values["True"])

    def eval_if3(self, a: AST, b: AST, c: AST,
                 values: dict[str, int]) -> int:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return (a_v & b_v) | ((values["True"] ^ a_v) & c_v)

    def eval_nif3(self, a: AST, b: AST, c: AST,
                  values: dict[str, int]) -> int:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return (((a_v & b_v)
                 | ((values["True"] ^ a_v) & c_v))
                ^ values["True"])


class EvalRustExpr(EvalEngine[str]):
    """A class to evaluate an expression."""

    def eval_not(self, node: AST, values: dict[str, str]) -> str:
        a_v = self.eval(node, values)
        return f"!{a_v}"

    def eval_and(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"({a_v} & {b_v})"

    def eval_or(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"({a_v} | {b_v})"

    def eval_xor(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"({a_v} ^ {b_v})"

    def eval_imp(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"(!{a_v} | {b_v})"

    def eval_nand(self, left: AST, right: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"!({a_v} & {b_v})"

    def eval_nor(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"!({a_v} | {b_v})"

    def eval_nxor(self, left: AST, right: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"!({a_v} ^ {b_v})"

    def eval_nimp(self, left: AST, right: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"({a_v} & !{b_v})"

    def eval_and3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"({a_v} & {b_v} & {c_v})"

    def eval_nand3(self, a: AST, b: AST, c: AST,
                   values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"!({a_v} & {b_v} & {c_v})"

    def eval_or3(self, a: AST, b: AST, c: AST,
                 values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"({a_v} | {b_v} | {c_v})"

    def eval_nor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"!({a_v} | {b_v} | {c_v})"

    def eval_xor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"({a_v} ^ {b_v} ^ {c_v})"

    def eval_nxor3(self, a: AST, b: AST, c: AST,
                   values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"(!{a_v} ^ {b_v} ^ {c_v})"

    def eval_maj3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"({a_v} & {b_v} | {a_v} & {c_v} | {b_v} & {c_v})"

    def eval_nmaj3(self, a: AST, b: AST, c: AST,
                   values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"!({a_v} & {b_v} | {a_v} & {c_v} | {b_v} & {c_v})"

    def eval_if3(self, a: AST, b: AST, c: AST,
                 values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"({a_v} & {b_v} | !{a_v} & {c_v})"

    def eval_nif3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"!({a_v} & {b_v} | !{a_v} & {c_v})"


class EvalHumanString(EvalEngine[str]):
    """A class to evaluate an expression."""

    def eval_not(self, node: AST, values: dict[str, str]) -> str:
        a_v = self.eval(node, values)
        return f"Not{a_v}"

    def eval_and(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"And{a_v}{b_v}"

    def eval_or(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"Or{a_v}{b_v}"

    def eval_xor(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"Xor{a_v}{b_v}"

    def eval_imp(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"Implies{a_v}{b_v}"

    def eval_nand(self, left: AST, right: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"NotAnd{a_v}{b_v}"

    def eval_nor(self, left: AST, right: AST, values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"NotOr{a_v}{b_v}"

    def eval_nxor(self, left: AST, right: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"Biimp{a_v}{b_v}"

    def eval_nimp(self, left: AST, right: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(left, values)
        b_v = self.eval(right, values)
        return f"NotImplies{a_v}{b_v}"

    def eval_and3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"And3{a_v}{b_v}{c_v}"

    def eval_nand3(self, a: AST, b: AST, c: AST,
                   values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"NotAnd3{a_v}{b_v}{c_v}"

    def eval_or3(self, a: AST, b: AST, c: AST,
                 values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"Or3{a_v}{b_v}{c_v}"

    def eval_nor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"NotOr3{a_v}{b_v}{c_v}"

    def eval_xor3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"Xor3{a_v}{b_v}{c_v}"

    def eval_nxor3(self, a: AST, b: AST, c: AST,
                   values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"NotXor3{a_v}{b_v}{c_v}"

    def eval_maj3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"Majority3{a_v}{b_v}{c_v}"

    def eval_nmaj3(self, a: AST, b: AST, c: AST,
                   values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"NotMajority3{a_v}{b_v}{c_v}"

    def eval_if3(self, a: AST, b: AST, c: AST,
                 values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"If{a_v}{b_v}{c_v}"

    def eval_nif3(self, a: AST, b: AST, c: AST,
                  values: dict[str, str]) -> str:
        a_v = self.eval(a, values)
        b_v = self.eval(b, values)
        c_v = self.eval(c, values)
        return f"NotIf{a_v}{b_v}{c_v}"


def compute_line_number(this_frame, guess: int) -> int:
    """Give line number of caller if we can."""
    return getframeinfo(this_frame).lineno if this_frame else guess


THIS_GAP = 3  # Gap between this_line and first element of test_cases
THIS_LINE = compute_line_number(currentframe(), 173)

test_cases: list[str] = [
    'True',
    'False',
    'a',
    'b',
    'c',
    '~a',
    '~b',
    '~c',
    'Implies(a, b)',
    'Implies(b, a)',
    '~Implies(a, b)',
    '~Implies(b, a)',
    '(a ^ b)',
    '(a & b)',
    '(a | b)',
    '~(a ^ b)',
    '~(a & b)',
    '~(a | b)',
    'b if a else c',
    'c if a else b',
    'a if b else c',
    'c if b else a',
    'a if c else b',
    'b if c else a',
    '~b if a else c',
    '~c if a else b',
    '~a if b else c',
    '~c if b else a',
    '~a if c else b',
    '~b if c else a',
    'b if a else ~c',
    'c if a else ~b',
    'a if b else ~c',
    'c if b else ~a',
    'a if c else ~b',
    'b if c else ~a',
    '~(b if a else c)',
    '~(c if a else b)',
    '~(a if b else c)',
    '~(c if b else a)',
    '~(a if c else b)',
    '~(b if c else a)',
    'a | b | c',
    'a & b & c',
    'a ^ b ^ c',
    '~(a ^ b ^ c)',
    '(a & b) | (a & c) | (b & c)',
    '~((b | c) if a else (b & c))',
]


def code_from_booleans(ast: Expression) -> int:
    """Get a 8-bit code."""
    eng = EvalBool()
    code = 0
    for c in [True, False]:
        for b in [True, False]:
            for a in [True, False]:
                value = eng.eval(ast, {
                    "a": a,
                    "b": b,
                    "c": c,
                    "True": True,
                    "False": False})
                code <<= 1
                code |= 1 if value else 0
    return code


def code_from_ints(ast: Expression) -> int:
    """Get a 8-bit code."""
    eng = EvalUint()
    code = eng.eval(ast, {
                    "a": 0xaa,
                    "b": 0xcc,
                    "c": 0xf0,
                    "True": 0xff,
                    "False": 0x00})
    return code


def rust_from_strs(ast: Expression) -> str:
    """Get a Rust expression."""
    eng = EvalRustExpr()
    rust = eng.eval(ast, {
                    "a": 'a',
                    "b": 'b',
                    "c": 'c',
                    "True": 'true',
                    "False": 'false'})
    return rust


def name_from_strs(ast: Expression) -> str:
    """Get a nice CamelCase name."""
    eng = EvalHumanString()
    name = eng.eval(ast, {
                    "a": 'A',
                    "b": 'B',
                    "c": 'C',
                    "True": 'True',
                    "False": 'False'})
    if len(name) == 1:
        name = "Id" + name
    return name


def test() -> None:
    """Test that the expressions parse."""
    for (line, str_expr) in enumerate(test_cases, start=THIS_LINE + THIS_GAP):
        try:
            ast: Expression = parse(str_expr, mode='eval')
            code1 = code_from_booleans(ast)
            code2 = code_from_ints(ast)
            rust = rust_from_strs(ast)
            name = name_from_strs(ast)
            print(f"code=0x{code2:02x}, expr=`{str_expr}`, rust=`{rust}`, "
                  f"name={name}, line={line}")
            if code1 != code2:
                print(f"### MISMATCH! from_bools={code1:02x}, "
                      f"from_ints={code2:02x}")
                print()
        except ValueError as err:
            print(f"line={line}, expr={str_expr}, "
                  f"ast={dump(ast, annotate_fields=True)}, err={err}")
            break


def main() -> None:
    """Test that the expressions parse."""
    test()


if __name__ == "__main__":
    main()
