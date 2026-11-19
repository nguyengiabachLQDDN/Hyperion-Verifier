"""From-scratch Lexer, Pratt/Recursive-Descent Parser & SSA Lifter for TypeScript/JS subset and Hyperion DSL."""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple

from hyperion.ir.ssa import (
    ArrayLoadOp,
    ArrayStoreOp,
    AssertOp,
    AssignOp,
    BasicBlock,
    BinaryOp,
    CallOp,
    CondBranchOp,
    Const,
    IRFunction,
    IRModule,
    IRType,
    IRValue,
    Instruction,
    JumpOp,
    PhiOp,
    ReturnOp,
    SSAVar,
    SinkOp,
    UnaryOp,
)

TS_TAINT_SOURCES = {
    "readInput",
    "getQueryParam",
    "readPacket",
    "untrustedInput",
    "reqBody",
    "prompt",
    "readLine",
}

TS_SANITIZERS = {
    "sanitize",
    "escapeSql",
    "escapeHtml",
    "validateInt",
    "clamp",
    "cleanInput",
}

TS_SECURITY_SINKS = {
    "eval": "code_injection",
    "exec": "os_command_injection",
    "cmdExec": "os_command_injection",
    "sqlExec": "sql_injection",
    "sqlQuery": "sql_injection",
    "bufferWrite": "buffer_overflow",
    "writeFile": "path_traversal",
}

KEYWORDS = {
    "function",
    "export",
    "async",
    "let",
    "const",
    "var",
    "if",
    "else",
    "while",
    "for",
    "return",
    "true",
    "false",
    "null",
    "undefined",
    "assert",
    "class",
    "interface",
    "type",
    "import",
    "from",
    "new",
}


@dataclass
class Token:
    kind: str  # IDENT, NUMBER, STRING, OP, PUNCT, KW, EOF
    value: str
    line: int


def tokenize_ts_dsl(src: str) -> List[Token]:
    """Zero-dependency lexical scanner supporting TypeScript/JS comments, strings, numbers, operators."""
    tokens: List[Token] = []
    n = len(src)
    i = 0
    line = 1
    multi_ops = (
        "===",
        "!==",
        "==",
        "!=",
        "<=",
        ">=",
        "&&",
        "||",
        "<<",
        ">>",
        "+=",
        "-=",
        "*=",
        "/=",
        "=>",
        "++",
        "--",
    )

    while i < n:
        ch = src[i]
        if ch == "\n":
            line += 1
            i += 1
            continue
        if ch in " \t\r":
            i += 1
            continue
        # Line comment
        if ch == "/" and i + 1 < n and src[i + 1] == "/":
            i += 2
            while i < n and src[i] != "\n":
                i += 1
            continue
        # Block comment
        if ch == "/" and i + 1 < n and src[i + 1] == "*":
            i += 2
            while i + 1 < n and not (src[i] == "*" and src[i + 1] == "/"):
                if src[i] == "\n":
                    line += 1
                i += 1
            i += 2
            continue
        # String literal
        if ch in ('"', "'", "`"):
            quote = ch
            i += 1
            buf = []
            while i < n and src[i] != quote:
                if src[i] == "\\" and i + 1 < n:
                    buf.append(src[i + 1])
                    i += 2
                    continue
                if src[i] == "\n":
                    line += 1
                buf.append(src[i])
                i += 1
            i += 1
            tokens.append(Token("STRING", "".join(buf), line))
            continue
        # Number literal
        if ch.isdigit():
            start = i
            is_hex = src[i : i + 2].lower() == "0x"
            if is_hex:
                i += 2
                while i < n and (src[i].isdigit() or src[i].lower() in "abcdef_"):
                    i += 1
            else:
                while i < n and (src[i].isdigit() or src[i] in "._"):
                    i += 1
            tokens.append(Token("NUMBER", src[start:i].replace("_", ""), line))
            continue
        # Identifier or keyword
        if ch.isalpha() or ch in ("_", "$"):
            start = i
            while i < n and (src[i].isalnum() or src[i] in ("_", "$")):
                i += 1
            word = src[start:i]
            kind = "KW" if word in KEYWORDS else "IDENT"
            tokens.append(Token(kind, word, line))
            continue
        # Multi-char operators
        matched = False
        for mop in multi_ops:
            if src.startswith(mop, i):
                tokens.append(Token("OP", mop, line))
                i += len(mop)
                matched = True
                break
        if matched:
            continue
        if ch in "+-*/%<>!&|^~=":
            tokens.append(Token("OP", ch, line))
            i += 1
            continue
        if ch in "(){}[];,.:?":
            tokens.append(Token("PUNCT", ch, line))
            i += 1
            continue
        i += 1

    tokens.append(Token("EOF", "", line))
    return tokens


# Lightweight AST nodes for TS/DSL
@dataclass
class TSExpr:
    line: int = 1


@dataclass
class TSLiteral(TSExpr):
    value: object = 0
    ir_type: IRType = IRType.INT


@dataclass
class TSVar(TSExpr):
    name: str = ""


@dataclass
class TSUnary(TSExpr):
    op: str = "-"
    operand: TSExpr = field(default_factory=TSExpr)


@dataclass
class TSBinary(TSExpr):
    op: str = "+"
    left: TSExpr = field(default_factory=TSExpr)
    right: TSExpr = field(default_factory=TSExpr)


@dataclass
class TSCall(TSExpr):
    callee: str = ""
    args: List[TSExpr] = field(default_factory=list)


@dataclass
class TSIndex(TSExpr):
    target: TSExpr = field(default_factory=TSExpr)
    index: TSExpr = field(default_factory=TSExpr)


@dataclass
class TSArrayLit(TSExpr):
    elements: List[TSExpr] = field(default_factory=list)


@dataclass
class TSStmt:
    line: int = 1


@dataclass
class TSAssign(TSStmt):
    target: str = ""
    index: Optional[TSExpr] = None
    value: TSExpr = field(default_factory=TSExpr)


@dataclass
class TSIf(TSStmt):
    cond: TSExpr = field(default_factory=TSExpr)
    then_body: List[TSStmt] = field(default_factory=list)
    else_body: List[TSStmt] = field(default_factory=list)


@dataclass
class TSWhile(TSStmt):
    cond: TSExpr = field(default_factory=TSExpr)
    body: List[TSStmt] = field(default_factory=list)


@dataclass
class TSFor(TSStmt):
    init: Optional[TSStmt] = None
    cond: Optional[TSExpr] = None
    step: Optional[TSStmt] = None
    body: List[TSStmt] = field(default_factory=list)


@dataclass
class TSReturn(TSStmt):
    value: Optional[TSExpr] = None


@dataclass
class TSAssert(TSStmt):
    cond: TSExpr = field(default_factory=TSExpr)
    message: str = "assert_failed"


@dataclass
class TSExprStmt(TSStmt):
    expr: TSExpr = field(default_factory=TSExpr)


@dataclass
class TSFunctionDecl:
    name: str
    params: List[str]
    body: List[TSStmt]
    line_start: int
    line_end: int


class _TSParser:
    """Pratt + recursive-descent parser for TypeScript/JS subset & Hyperion DSL."""

    PRECEDENCE = {
        "||": 1,
        "&&": 2,
        "|": 3,
        "^": 4,
        "&": 5,
        "==": 6,
        "!=": 6,
        "===": 6,
        "!==": 6,
        "<": 7,
        "<=": 7,
        ">": 7,
        ">=": 7,
        "<<": 8,
        ">>": 8,
        "+": 9,
        "-": 9,
        "*": 10,
        "/": 10,
        "%": 10,
    }

    def __init__(self, tokens: List[Token]) -> None:
        self.tokens = tokens
        self.pos = 0

    def cur(self) -> Token:
        return self.tokens[min(self.pos, len(self.tokens) - 1)]

    def peek(self, offset: int = 1) -> Token:
        idx = min(self.pos + offset, len(self.tokens) - 1)
        return self.tokens[idx]

    def advance(self) -> Token:
        t = self.cur()
        self.pos += 1
        return t

    def match(self, kind: str, value: Optional[str] = None) -> bool:
        t = self.cur()
        if t.kind != kind:
            return False
        if value is not None and t.value != value:
            return False
        self.pos += 1
        return True

    def skip_type_annotation(self) -> None:
        """Skip `: TypeExpr` annotations in TypeScript parameters/variables."""
        if self.cur().kind == "PUNCT" and self.cur().value == ":":
            self.advance()
            depth_angle = 0
            depth_paren = 0
            depth_brack = 0
            while self.cur().kind != "EOF":
                t = self.cur()
                if t.value in ("<",):
                    depth_angle += 1
                elif t.value == ">" and depth_angle > 0:
                    depth_angle -= 1
                elif t.value == "(":
                    depth_paren += 1
                elif t.value == ")" and depth_paren > 0:
                    depth_paren -= 1
                elif t.value == "[":
                    depth_brack += 1
                elif t.value == "]" and depth_brack > 0:
                    depth_brack -= 1
                elif (
                    depth_angle == 0
                    and depth_paren == 0
                    and depth_brack == 0
                    and t.value in (",", ")", "=", "{", ";")
                ):
                    break
                self.advance()

    def skip_balanced(self, open_ch: str, close_ch: str) -> None:
        if self.cur().value != open_ch:
            return
        depth = 0
        while self.cur().kind != "EOF":
            v = self.advance().value
            if v == open_ch:
                depth += 1
            elif v == close_ch:
                depth -= 1
                if depth <= 0:
                    break

    def parse_program(self) -> List[TSFunctionDecl]:
        fns: List[TSFunctionDecl] = []
        while self.cur().kind != "EOF":
            t = self.cur()
            if t.kind == "KW" and t.value in ("export", "async"):
                self.advance()
                continue
            if t.kind == "KW" and t.value in ("interface", "type"):
                self.advance()
                while self.cur().kind != "EOF" and self.cur().value not in ("{", ";"):
                    self.advance()
                if self.cur().value == "{":
                    self.skip_balanced("{", "}")
                elif self.cur().value == ";":
                    self.advance()
                continue
            if t.kind == "KW" and t.value == "import":
                while self.cur().kind != "EOF" and self.cur().value != ";":
                    if self.cur().line > t.line and self.cur().kind == "KW":
                        break
                    self.advance()
                self.match("PUNCT", ";")
                continue
            if t.kind == "KW" and t.value == "function":
                fn = self.parse_function()
                if fn is not None:
                    fns.append(fn)
                continue
            if t.kind == "KW" and t.value == "class":
                fns.extend(self.parse_class_methods())
                continue
            self.advance()
        return fns

    def parse_class_methods(self) -> List[TSFunctionDecl]:
        methods: List[TSFunctionDecl] = []
        self.advance()  # class
        cls_name = self.advance().value if self.cur().kind == "IDENT" else "AnonClass"
        while self.cur().kind != "EOF" and self.cur().value != "{":
            self.advance()
        if not self.match("PUNCT", "{"):
            return methods
        while self.cur().kind != "EOF" and self.cur().value != "}":
            while self.cur().kind == "IDENT" and self.cur().value in ("public", "private", "protected", "static", "readonly"):
                self.advance()
            if self.cur().kind == "KW" and self.cur().value == "async":
                self.advance()
            if self.cur().kind == "IDENT" and self.peek().value == "(":
                fn = self.parse_method_sig_and_body(prefix=f"{cls_name}.")
                if fn is not None:
                    methods.append(fn)
            else:
                self.advance()
        self.match("PUNCT", "}")
        return methods

    def parse_function(self) -> Optional[TSFunctionDecl]:
        start_tok = self.advance()  # function
        if self.cur().kind != "IDENT":
            return None
        name = self.advance().value
        return self._finish_function(name, start_tok.line)

    def parse_method_sig_and_body(self, prefix: str) -> Optional[TSFunctionDecl]:
        name_tok = self.advance()
        return self._finish_function(f"{prefix}{name_tok.value}", name_tok.line)

    def _finish_function(self, name: str, start_line: int) -> Optional[TSFunctionDecl]:
        if self.cur().value == "<":
            self.skip_balanced("<", ">")
        if not self.match("PUNCT", "("):
            return None
        params: List[str] = []
        while self.cur().kind != "EOF" and self.cur().value != ")":
            if self.cur().kind == "IDENT":
                params.append(self.advance().value)
                self.skip_type_annotation()
                if self.match("OP", "="):
                    self.parse_expr()
            else:
                self.advance()
            self.match("PUNCT", ",")
        self.match("PUNCT", ")")
        self.skip_type_annotation()
        if not self.match("PUNCT", "{"):
            return None
        body, end_line = self.parse_block()
        return TSFunctionDecl(
            name=name, params=params, body=body, line_start=start_line, line_end=end_line
        )

    def parse_block(self) -> Tuple[List[TSStmt], int]:
        stmts: List[TSStmt] = []
        end_line = self.cur().line
        while self.cur().kind != "EOF" and self.cur().value != "}":
            stmt = self.parse_stmt()
            if stmt is not None:
                stmts.append(stmt)
                end_line = stmt.line
        if self.cur().value == "}":
            end_line = self.cur().line
            self.advance()
        return stmts, end_line

    def parse_stmt(self) -> Optional[TSStmt]:
        t = self.cur()
        if t.kind == "PUNCT" and t.value == ";":
            self.advance()
            return None
        if t.kind == "KW" and t.value in ("let", "const", "var"):
            self.advance()
            if self.cur().kind != "IDENT":
                self.advance()
                return None
            name = self.advance().value
            self.skip_type_annotation()
            val: TSExpr = TSLiteral(line=t.line, value=0, ir_type=IRType.INT)
            if self.match("OP", "="):
                val = self.parse_expr()
            self.match("PUNCT", ";")
            return TSAssign(line=t.line, target=name, value=val)

        if t.kind == "KW" and t.value == "if":
            self.advance()
            self.match("PUNCT", "(")
            cond = self.parse_expr()
            self.match("PUNCT", ")")
            then_body = self._parse_stmt_or_block()
            else_body: List[TSStmt] = []
            if self.match("KW", "else"):
                else_body = self._parse_stmt_or_block()
            return TSIf(line=t.line, cond=cond, then_body=then_body, else_body=else_body)

        if t.kind == "KW" and t.value == "while":
            self.advance()
            self.match("PUNCT", "(")
            cond = self.parse_expr()
            self.match("PUNCT", ")")
            body = self._parse_stmt_or_block()
            return TSWhile(line=t.line, cond=cond, body=body)

        if t.kind == "KW" and t.value == "for":
            self.advance()
            self.match("PUNCT", "(")
            init = self.parse_stmt() if self.cur().value != ";" else None
            if init is None:
                self.match("PUNCT", ";")
            cond = self.parse_expr() if self.cur().value != ";" else None
            self.match("PUNCT", ";")
            step = self._parse_simple_assign_or_expr() if self.cur().value != ")" else None
            self.match("PUNCT", ")")
            body = self._parse_stmt_or_block()
            return TSFor(line=t.line, init=init, cond=cond, step=step, body=body)

        if t.kind == "KW" and t.value == "return":
            self.advance()
            val = None
            if self.cur().value not in (";", "}"):
                val = self.parse_expr()
            self.match("PUNCT", ";")
            return TSReturn(line=t.line, value=val)

        if t.kind == "KW" and t.value == "assert":
            self.advance()
            self.match("PUNCT", "(")
            cond = self.parse_expr()
            msg = "assert_failed"
            if self.match("PUNCT", ",") and self.cur().kind == "STRING":
                msg = self.advance().value
            self.match("PUNCT", ")")
            self.match("PUNCT", ";")
            return TSAssert(line=t.line, cond=cond, message=msg)

        stmt = self._parse_simple_assign_or_expr()
        self.match("PUNCT", ";")
        return stmt

    def _parse_stmt_or_block(self) -> List[TSStmt]:
        if self.match("PUNCT", "{"):
            body, _ = self.parse_block()
            return body
        s = self.parse_stmt()
        return [s] if s is not None else []

    def _parse_simple_assign_or_expr(self) -> TSStmt:
        t = self.cur()
        if t.kind == "IDENT":
            nxt = self.peek()
            if nxt.kind == "OP" and nxt.value in ("=", "+=", "-=", "*=", "/="):
                name = self.advance().value
                op = self.advance().value
                rhs = self.parse_expr()
                if op != "=":
                    rhs = TSBinary(line=t.line, op=op[0], left=TSVar(line=t.line, name=name), right=rhs)
                return TSAssign(line=t.line, target=name, value=rhs)
            if nxt.kind == "OP" and nxt.value in ("++", "--"):
                name = self.advance().value
                op = self.advance().value[0]
                rhs = TSBinary(
                    line=t.line,
                    op=op,
                    left=TSVar(line=t.line, name=name),
                    right=TSLiteral(line=t.line, value=1, ir_type=IRType.INT),
                )
                return TSAssign(line=t.line, target=name, value=rhs)
        expr = self.parse_expr()
        if isinstance(expr, TSIndex) and self.match("OP", "="):
            val = self.parse_expr()
            tname = expr.target.name if isinstance(expr.target, TSVar) else "arr"
            return TSAssign(line=t.line, target=tname, index=expr.index, value=val)
        return TSExprStmt(line=t.line, expr=expr)

    def parse_expr(self, min_prec: int = 1) -> TSExpr:
        left = self.parse_unary()
        while self.cur().kind == "OP" and self.cur().value in self.PRECEDENCE:
            op = self.cur().value
            prec = self.PRECEDENCE[op]
            if prec < min_prec:
                break
            line = self.advance().line
            right = self.parse_expr(prec + 1)
            left = TSBinary(line=line, op=op, left=left, right=right)
        return left

    def parse_unary(self) -> TSExpr:
        t = self.cur()
        if t.kind == "OP" and t.value in ("-", "!", "~"):
            self.advance()
            return TSUnary(line=t.line, op=t.value, operand=self.parse_unary())
        return self.parse_postfix()

    def parse_postfix(self) -> TSExpr:
        expr = self.parse_primary()
        while True:
            t = self.cur()
            if self.match("PUNCT", "("):
                args: List[TSExpr] = []
                while self.cur().kind != "EOF" and self.cur().value != ")":
                    args.append(self.parse_expr())
                    self.match("PUNCT", ",")
                self.match("PUNCT", ")")
                cname = expr.name if isinstance(expr, TSVar) else "call"
                expr = TSCall(line=t.line, callee=cname, args=args)
            elif self.match("PUNCT", "["):
                idx = self.parse_expr()
                self.match("PUNCT", "]")
                expr = TSIndex(line=t.line, target=expr, index=idx)
            elif self.match("PUNCT", "."):
                prop = self.advance().value if self.cur().kind == "IDENT" else "prop"
                base = expr.name if isinstance(expr, TSVar) else "obj"
                expr = TSVar(line=t.line, name=f"{base}.{prop}")
            else:
                break
        return expr

    def parse_primary(self) -> TSExpr:
        t = self.cur()
        if t.kind == "NUMBER":
            self.advance()
            if "." in t.value:
                return TSLiteral(line=t.line, value=float(t.value), ir_type=IRType.FLOAT)
            val = int(t.value, 16) if t.value.lower().startswith("0x") else int(t.value)
            return TSLiteral(line=t.line, value=val, ir_type=IRType.INT)
        if t.kind == "STRING":
            self.advance()
            return TSLiteral(line=t.line, value=t.value, ir_type=IRType.STRING)
        if t.kind == "KW" and t.value in ("true", "false"):
            self.advance()
            return TSLiteral(line=t.line, value=(t.value == "true"), ir_type=IRType.BOOL)
        if t.kind == "KW" and t.value in ("null", "undefined"):
            self.advance()
            return TSLiteral(line=t.line, value=0, ir_type=IRType.ANY)
        if t.kind == "IDENT":
            self.advance()
            return TSVar(line=t.line, name=t.value)
        if self.match("PUNCT", "("):
            inner = self.parse_expr()
            self.match("PUNCT", ")")
            return inner
        if self.match("PUNCT", "["):
            elems: List[TSExpr] = []
            while self.cur().kind != "EOF" and self.cur().value != "]":
                elems.append(self.parse_expr())
                self.match("PUNCT", ",")
            self.match("PUNCT", "]")
            return TSArrayLit(line=t.line, elements=elems)
        self.advance()
        return TSLiteral(line=t.line, value=0, ir_type=IRType.INT)


class _TSSABuilder:
    def __init__(self, fn: IRFunction) -> None:
        self.fn = fn
        self._next_block_id = 0
        self._next_inst_id = 1
        self._versions: Dict[str, int] = {}
        self._env: Dict[str, SSAVar] = {}

        entry = self.new_block("entry")
        self.fn.entry_id = entry.id
        self.cur_block = entry

    def new_block(self, label: str) -> BasicBlock:
        bid = self._next_block_id
        self._next_block_id += 1
        blk = BasicBlock(id=bid, label=label)
        self.fn.blocks[bid] = blk
        return blk

    def new_var(self, base: str, ir_type: IRType = IRType.ANY) -> SSAVar:
        ver = self._versions.get(base, 0)
        self._versions[base] = ver + 1
        return SSAVar(name=base, version=ver, ir_type=ir_type)

    def emit(self, ins: Instruction, block: Optional[BasicBlock] = None) -> Instruction:
        target = block or self.cur_block
        ins.id = self._next_inst_id
        self._next_inst_id += 1
        target.instructions.append(ins)
        return ins

    def get_var(self, name: str) -> IRValue:
        if name in self._env:
            return self._env[name]
        v = self.new_var(name, IRType.ANY)
        self._env[name] = v
        return v

    def set_var(self, name: str, val: IRValue, line: int) -> SSAVar:
        d = self.new_var(name, val.ir_type)
        self.emit(AssignOp(dest=d, line=line, src=val))
        self._env[name] = d
        return d

    def link(self, src_id: int, dst_id: int) -> None:
        src = self.fn.blocks[src_id]
        dst = self.fn.blocks[dst_id]
        if dst_id not in src.succs:
            src.succs.append(dst_id)
        if src_id not in dst.preds:
            dst.preds.append(src_id)


def _normalize_ts_op(op: str) -> str:
    if op == "===":
        return "=="
    if op == "!==":
        return "!="
    if op == "&&":
        return "and"
    if op == "||":
        return "or"
    return op


def _lower_ts_expr(b: _TSSABuilder, expr: TSExpr) -> IRValue:
    if isinstance(expr, TSLiteral):
        return Const(value=expr.value, ir_type=expr.ir_type)
    if isinstance(expr, TSVar):
        return b.get_var(expr.name)
    if isinstance(expr, TSUnary):
        opd = _lower_ts_expr(b, expr.operand)
        op_s = "not" if expr.op == "!" else expr.op
        dest = b.new_var("u", IRType.BOOL if op_s == "not" else opd.ir_type)
        b.emit(UnaryOp(dest=dest, line=expr.line, op=op_s, operand=opd))
        return dest
    if isinstance(expr, TSBinary):
        lv = _lower_ts_expr(b, expr.left)
        rv = _lower_ts_expr(b, expr.right)
        op_s = _normalize_ts_op(expr.op)
        dest = b.new_var("t", IRType.INT)
        b.emit(BinaryOp(dest=dest, line=expr.line, op=op_s, left=lv, right=rv))
        return dest
    if isinstance(expr, TSCall):
        short = expr.callee.split(".")[-1]
        args = [_lower_ts_expr(b, a) for a in expr.args]
        dest = b.new_var("call", IRType.ANY)
        if short in TS_SECURITY_SINKS:
            b.emit(SinkOp(dest=dest, line=expr.line, sink_kind=TS_SECURITY_SINKS[short], args=args))
        else:
            b.emit(
                CallOp(
                    dest=dest,
                    line=expr.line,
                    callee=short,
                    args=args,
                    is_taint_source=(short in TS_TAINT_SOURCES or short.startswith("untrusted")),
                    is_sanitizer=(short in TS_SANITIZERS),
                )
            )
        return dest
    if isinstance(expr, TSIndex):
        arr = _lower_ts_expr(b, expr.target)
        idx = _lower_ts_expr(b, expr.index)
        known_len = b.fn.array_lengths.get(arr.name) if isinstance(arr, SSAVar) else None
        dest = b.new_var("elem", IRType.ANY)
        b.emit(ArrayLoadOp(dest=dest, line=expr.line, array=arr, index=idx, known_length=known_len))
        return dest
    if isinstance(expr, TSArrayLit):
        dest = b.new_var("arr", IRType.ARRAY)
        b.fn.array_lengths[dest.name] = len(expr.elements)
        b.emit(
            CallOp(
                dest=dest,
                line=expr.line,
                callee="alloc_array",
                args=[Const(value=len(expr.elements), ir_type=IRType.INT)],
            )
        )
        return dest
    return Const(value=0, ir_type=IRType.INT)


def _lower_ts_stmts(b: _TSSABuilder, stmts: List[TSStmt]) -> None:
    for stmt in stmts:
        if b.cur_block.is_terminated():
            break
        ln = stmt.line
        if isinstance(stmt, TSAssign):
            val = _lower_ts_expr(b, stmt.value)
            if stmt.index is not None:
                arr = b.get_var(stmt.target)
                idx = _lower_ts_expr(b, stmt.index)
                known_len = b.fn.array_lengths.get(stmt.target)
                b.emit(ArrayStoreOp(line=ln, array=arr, index=idx, value=val, known_length=known_len))
            else:
                if isinstance(stmt.value, TSArrayLit):
                    b.fn.array_lengths[stmt.target] = len(stmt.value.elements)
                b.set_var(stmt.target, val, ln)
        elif isinstance(stmt, TSExprStmt):
            _lower_ts_expr(b, stmt.expr)
        elif isinstance(stmt, TSAssert):
            cond = _lower_ts_expr(b, stmt.cond)
            b.emit(AssertOp(line=ln, cond=cond, message=stmt.message))
        elif isinstance(stmt, TSReturn):
            val = _lower_ts_expr(b, stmt.value) if stmt.value is not None else None
            b.emit(ReturnOp(line=ln, value=val))
        elif isinstance(stmt, TSIf):
            cond = _lower_ts_expr(b, stmt.cond)
            pre_env = dict(b._env)
            entry_blk = b.cur_block
            then_blk = b.new_block(f"if_then_{ln}")
            else_blk = b.new_block(f"if_else_{ln}")
            join_blk = b.new_block(f"if_join_{ln}")
            b.emit(
                CondBranchOp(line=ln, cond=cond, true_target=then_blk.id, false_target=else_blk.id),
                block=entry_blk,
            )
            b.link(entry_blk.id, then_blk.id)
            b.link(entry_blk.id, else_blk.id)

            b.cur_block = then_blk
            b._env = dict(pre_env)
            _lower_ts_stmts(b, stmt.then_body)
            then_end = b.cur_block
            then_falls = not then_end.is_terminated()
            if then_falls:
                b.emit(JumpOp(line=ln, target=join_blk.id))
                b.link(then_end.id, join_blk.id)
            then_env = dict(b._env)

            b.cur_block = else_blk
            b._env = dict(pre_env)
            _lower_ts_stmts(b, stmt.else_body)
            else_end = b.cur_block
            else_falls = not else_end.is_terminated()
            if else_falls:
                b.emit(JumpOp(line=ln, target=join_blk.id))
                b.link(else_end.id, join_blk.id)
            else_env = dict(b._env)

            b.cur_block = join_blk
            if then_falls and else_falls:
                merged: Dict[str, SSAVar] = {}
                for k in sorted(set(then_env) | set(else_env)):
                    va, vb = then_env.get(k), else_env.get(k)
                    if va and vb and va.key() != vb.key():
                        pv = b.new_var(k, va.ir_type)
                        b.emit(PhiOp(dest=pv, line=ln, incomings=[(then_end.id, va), (else_end.id, vb)]))
                        merged[k] = pv
                    elif va or vb:
                        merged[k] = va or vb  # type: ignore[assignment]
                b._env = merged
            elif then_falls:
                b._env = then_env
            elif else_falls:
                b._env = else_env
            else:
                b.emit(ReturnOp(line=ln, value=None))

        elif isinstance(stmt, (TSWhile, TSFor)):
            if isinstance(stmt, TSFor) and stmt.init is not None:
                _lower_ts_stmts(b, [stmt.init])
            pre_blk = b.cur_block
            pre_env = dict(b._env)
            hdr_blk = b.new_block(f"loop_hdr_{ln}")
            body_blk = b.new_block(f"loop_body_{ln}")
            exit_blk = b.new_block(f"loop_exit_{ln}")
            if not b.cur_block.is_terminated():
                b.emit(JumpOp(line=ln, target=hdr_blk.id))
                b.link(b.cur_block.id, hdr_blk.id)

            b.cur_block = hdr_blk
            cond_expr = stmt.cond if stmt.cond is not None else TSLiteral(line=ln, value=True, ir_type=IRType.BOOL)
            cond_v = _lower_ts_expr(b, cond_expr)
            b.emit(CondBranchOp(line=ln, cond=cond_v, true_target=body_blk.id, false_target=exit_blk.id))
            b.link(hdr_blk.id, body_blk.id)
            b.link(hdr_blk.id, exit_blk.id)

            b.cur_block = body_blk
            _lower_ts_stmts(b, stmt.body)
            if isinstance(stmt, TSFor) and stmt.step is not None and not b.cur_block.is_terminated():
                _lower_ts_stmts(b, [stmt.step])
            back_id = b.cur_block.id
            if not b.cur_block.is_terminated():
                b.emit(JumpOp(line=ln, target=hdr_blk.id))
                b.link(back_id, hdr_blk.id)
            post_env = dict(b._env)

            phis: List[PhiOp] = []
            for k, post_v in post_env.items():
                pre_v = pre_env.get(k)
                if pre_v and post_v.key() != pre_v.key():
                    pv = b.new_var(k, pre_v.ir_type)
                    phis.append(
                        PhiOp(
                            id=b._next_inst_id,
                            dest=pv,
                            line=ln,
                            incomings=[(pre_blk.id, pre_v), (back_id, post_v)],
                        )
                    )
                    b._next_inst_id += 1
                    pre_env[k] = pv
            if phis:
                hdr_blk.instructions = phis + hdr_blk.instructions

            b.cur_block = exit_blk
            b._env = pre_env


def parse_ts_dsl_source(
    source_code: str, module_name: str = "ts_module", source_file: str = "<memory>"
) -> IRModule:
    """Lex, parse, and lift TypeScript/JS/DSL functions into Unified SSA IR."""
    mod = IRModule(
        name=module_name,
        language="typescript",
        source_file=source_file,
        source_code=source_code,
    )
    tokens = tokenize_ts_dsl(source_code)
    parser = _TSParser(tokens)
    decls = parser.parse_program()
    lines = source_code.splitlines()

    for decl in decls:
        snippet = "\n".join(lines[max(0, decl.line_start - 1) : decl.line_end])
        fn = IRFunction(
            name=decl.name,
            source_lang="typescript",
            source_file=source_file,
            line_start=decl.line_start,
            line_end=decl.line_end,
            source_code=snippet,
        )
        builder = _TSSABuilder(fn)
        for p in decl.params:
            pv = builder.new_var(p, IRType.ANY)
            fn.params.append(pv)
            builder._env[p] = pv
        _lower_ts_stmts(builder, decl.body)
        if not builder.cur_block.is_terminated():
            builder.emit(ReturnOp(line=decl.line_end, value=None))
        mod.functions.append(fn)

    return mod
