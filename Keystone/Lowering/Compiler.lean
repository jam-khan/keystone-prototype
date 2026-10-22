import Keystone.Lowering.Language

namespace Keystone.Lowering

/-- Expression trees become postfix stack operations. -/
def compileExpr : Expr → List Instr
  | .lit value => [.lit value]
  | .arg parameter => [.arg parameter]
  | .local id => [.local id]
  | .bin op lhs rhs => compileExpr lhs ++ compileExpr rhs ++ [.bin op]

/-- Structured guards become balanced predicate regions. -/
def compile : Cmd → List Instr
  | .skip => []
  | .seq first second => compile first ++ compile second
  | .set id value => compileExpr value ++ [.set id]
  | .loadPageTable id index => compileExpr index ++ [.loadPageTable id]
  | .loadKVCache id index => compileExpr index ++ [.loadKVCache id]
  | .store index value => compileExpr index ++ compileExpr value ++ [.store]
  | .whenLt lhs rhs body =>
    compileExpr lhs ++ compileExpr rhs ++ [.enterMask] ++ compile body ++ [.leaveMask]

end Keystone.Lowering
