"""Unified Static Single Assignment (SSA) IR nodes, BasicBlocks, Functions, and Modules."""

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Dict, List, Optional, Tuple


class IRType(str, Enum):
    INT = "int"
    FLOAT = "float"
    BOOL = "bool"
    STRING = "str"
    ARRAY = "array"
    MAP = "map"
    ANY = "any"
    VOID = "void"


@dataclass(frozen=True)
class IRValue:
    """Base value in SSA IR."""

    ir_type: IRType = IRType.ANY

    def format(self) -> str:
        return "?"


@dataclass(frozen=True)
class SSAVar(IRValue):
    """Versioned SSA variable (e.g., x_3)."""

    name: str = "tmp"
    version: int = 0

    def key(self) -> str:
        return f"{self.name}_{self.version}"

    def format(self) -> str:
        return f"%{self.name}_{self.version}"


@dataclass(frozen=True)
class Const(IRValue):
    """Constant literal value."""

    value: Any = 0

    def format(self) -> str:
        if isinstance(self.value, str):
            return repr(self.value)
        return str(self.value)


@dataclass
class Instruction:
    """Base SSA instruction."""

    id: int = 0
    dest: Optional[SSAVar] = None
    line: int = 0

    def uses(self) -> List[IRValue]:
        return []

    def defs(self) -> List[SSAVar]:
        return [self.dest] if self.dest is not None else []

    def clone(self) -> "Instruction":
        raise NotImplementedError

    def format(self) -> str:
        return self.__class__.__name__


@dataclass
class AssignOp(Instruction):
    src: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.INT))

    def uses(self) -> List[IRValue]:
        return [self.src]

    def clone(self) -> "AssignOp":
        return AssignOp(id=self.id, dest=self.dest, line=self.line, src=self.src)

    def format(self) -> str:
        d = self.dest.format() if self.dest else "_"
        return f"{d} = {self.src.format()}"


@dataclass
class BinaryOp(Instruction):
    op: str = "+"
    left: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.INT))
    right: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.INT))

    def uses(self) -> List[IRValue]:
        return [self.left, self.right]

    def clone(self) -> "BinaryOp":
        return BinaryOp(
            id=self.id,
            dest=self.dest,
            line=self.line,
            op=self.op,
            left=self.left,
            right=self.right,
        )

    def format(self) -> str:
        d = self.dest.format() if self.dest else "_"
        return f"{d} = {self.left.format()} {self.op} {self.right.format()}"


@dataclass
class UnaryOp(Instruction):
    op: str = "-"
    operand: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.INT))

    def uses(self) -> List[IRValue]:
        return [self.operand]

    def clone(self) -> "UnaryOp":
        return UnaryOp(
            id=self.id, dest=self.dest, line=self.line, op=self.op, operand=self.operand
        )

    def format(self) -> str:
        d = self.dest.format() if self.dest else "_"
        return f"{d} = {self.op}{self.operand.format()}"


@dataclass
class PhiOp(Instruction):
    """SSA Phi node merging incoming values from predecessor blocks."""

    incomings: List[Tuple[int, IRValue]] = field(default_factory=list)

    def uses(self) -> List[IRValue]:
        return [val for _, val in self.incomings]

    def clone(self) -> "PhiOp":
        return PhiOp(
            id=self.id,
            dest=self.dest,
            line=self.line,
            incomings=list(self.incomings),
        )

    def format(self) -> str:
        d = self.dest.format() if self.dest else "_"
        args = ", ".join(f"[B{bid}: {val.format()}]" for bid, val in self.incomings)
        return f"{d} = phi({args})"


@dataclass
class CondBranchOp(Instruction):
    cond: IRValue = field(default_factory=lambda: Const(value=True, ir_type=IRType.BOOL))
    true_target: int = 0
    false_target: int = 0

    def uses(self) -> List[IRValue]:
        return [self.cond]

    def clone(self) -> "CondBranchOp":
        return CondBranchOp(
            id=self.id,
            dest=None,
            line=self.line,
            cond=self.cond,
            true_target=self.true_target,
            false_target=self.false_target,
        )

    def format(self) -> str:
        return f"br {self.cond.format()} ? B{self.true_target} : B{self.false_target}"


@dataclass
class JumpOp(Instruction):
    target: int = 0

    def clone(self) -> "JumpOp":
        return JumpOp(id=self.id, dest=None, line=self.line, target=self.target)

    def format(self) -> str:
        return f"jmp B{self.target}"


@dataclass
class CallOp(Instruction):
    callee: str = "fn"
    args: List[IRValue] = field(default_factory=list)
    is_taint_source: bool = False
    is_sanitizer: bool = False

    def uses(self) -> List[IRValue]:
        return list(self.args)

    def clone(self) -> "CallOp":
        return CallOp(
            id=self.id,
            dest=self.dest,
            line=self.line,
            callee=self.callee,
            args=list(self.args),
            is_taint_source=self.is_taint_source,
            is_sanitizer=self.is_sanitizer,
        )

    def format(self) -> str:
        d = f"{self.dest.format()} = " if self.dest else ""
        a = ", ".join(x.format() for x in self.args)
        tag = " [SRC]" if self.is_taint_source else (" [SAN]" if self.is_sanitizer else "")
        return f"{d}call {self.callee}({a}){tag}"


@dataclass
class SinkOp(Instruction):
    """Represents a security or correctness sink (SQL, OS cmd, eval, buffer write)."""

    sink_kind: str = "generic_sink"
    args: List[IRValue] = field(default_factory=list)

    def uses(self) -> List[IRValue]:
        return list(self.args)

    def clone(self) -> "SinkOp":
        return SinkOp(
            id=self.id,
            dest=self.dest,
            line=self.line,
            sink_kind=self.sink_kind,
            args=list(self.args),
        )

    def format(self) -> str:
        d = f"{self.dest.format()} = " if self.dest else ""
        a = ", ".join(x.format() for x in self.args)
        return f"{d}sink[{self.sink_kind}]({a})"


@dataclass
class AssertOp(Instruction):
    cond: IRValue = field(default_factory=lambda: Const(value=True, ir_type=IRType.BOOL))
    message: str = "assertion"

    def uses(self) -> List[IRValue]:
        return [self.cond]

    def clone(self) -> "AssertOp":
        return AssertOp(
            id=self.id, dest=None, line=self.line, cond=self.cond, message=self.message
        )

    def format(self) -> str:
        return f"assert {self.cond.format()} ({self.message})"


@dataclass
class ArrayLoadOp(Instruction):
    array: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.ARRAY))
    index: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.INT))
    known_length: Optional[int] = None

    def uses(self) -> List[IRValue]:
        return [self.array, self.index]

    def clone(self) -> "ArrayLoadOp":
        return ArrayLoadOp(
            id=self.id,
            dest=self.dest,
            line=self.line,
            array=self.array,
            index=self.index,
            known_length=self.known_length,
        )

    def format(self) -> str:
        d = self.dest.format() if self.dest else "_"
        return f"{d} = load {self.array.format()}[{self.index.format()}]"


@dataclass
class ArrayStoreOp(Instruction):
    array: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.ARRAY))
    index: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.INT))
    value: IRValue = field(default_factory=lambda: Const(value=0, ir_type=IRType.ANY))
    known_length: Optional[int] = None

    def uses(self) -> List[IRValue]:
        return [self.array, self.index, self.value]

    def clone(self) -> "ArrayStoreOp":
        return ArrayStoreOp(
            id=self.id,
            dest=None,
            line=self.line,
            array=self.array,
            index=self.index,
            value=self.value,
            known_length=self.known_length,
        )

    def format(self) -> str:
        return f"store {self.array.format()}[{self.index.format()}] = {self.value.format()}"


@dataclass
class ReturnOp(Instruction):
    value: Optional[IRValue] = None

    def uses(self) -> List[IRValue]:
        return [self.value] if self.value is not None else []

    def clone(self) -> "ReturnOp":
        return ReturnOp(id=self.id, dest=None, line=self.line, value=self.value)

    def format(self) -> str:
        return f"ret {self.value.format()}" if self.value is not None else "ret void"


@dataclass
class BasicBlock:
    id: int
    label: str
    instructions: List[Instruction] = field(default_factory=list)
    preds: List[int] = field(default_factory=list)
    succs: List[int] = field(default_factory=list)
    dom_frontier: List[int] = field(default_factory=list)

    def is_terminated(self) -> bool:
        if not self.instructions:
            return False
        return isinstance(self.instructions[-1], (CondBranchOp, JumpOp, ReturnOp))

    def clone(self) -> "BasicBlock":
        return BasicBlock(
            id=self.id,
            label=self.label,
            instructions=[ins.clone() for ins in self.instructions],
            preds=list(self.preds),
            succs=list(self.succs),
            dom_frontier=list(self.dom_frontier),
        )


@dataclass
class IRFunction:
    name: str
    params: List[SSAVar] = field(default_factory=list)
    blocks: Dict[int, BasicBlock] = field(default_factory=dict)
    entry_id: int = 0
    source_lang: str = "python"
    source_file: str = "<memory>"
    line_start: int = 1
    line_end: int = 1
    source_code: str = ""
    array_lengths: Dict[str, int] = field(default_factory=dict)

    def instruction_count(self) -> int:
        return sum(len(b.instructions) for b in self.blocks.values())

    def dump_ssa(self) -> str:
        lines = [
            f"fn {self.name}({', '.join(p.format() for p in self.params)}) [{self.source_lang} @ {self.source_file}:{self.line_start}]"
        ]
        for bid in sorted(self.blocks.keys()):
            blk = self.blocks[bid]
            preds_s = ",".join(f"B{p}" for p in blk.preds)
            succs_s = ",".join(f"B{s}" for s in blk.succs)
            lines.append(f"  B{bid} ({blk.label})  preds=[{preds_s}] succs=[{succs_s}]:")
            for ins in blk.instructions:
                lines.append(f"    {ins.format()}")
        return "\n".join(lines)

    def clone(self) -> "IRFunction":
        return IRFunction(
            name=self.name,
            params=list(self.params),
            blocks={bid: blk.clone() for bid, blk in self.blocks.items()},
            entry_id=self.entry_id,
            source_lang=self.source_lang,
            source_file=self.source_file,
            line_start=self.line_start,
            line_end=self.line_end,
            source_code=self.source_code,
            array_lengths=dict(self.array_lengths),
        )


@dataclass
class IRModule:
    name: str
    language: str
    source_file: str
    source_code: str
    functions: List[IRFunction] = field(default_factory=list)
    parse_errors: List[str] = field(default_factory=list)

    def total_instructions(self) -> int:
        return sum(fn.instruction_count() for fn in self.functions)

    def total_blocks(self) -> int:
        return sum(len(fn.blocks) for fn in self.functions)
