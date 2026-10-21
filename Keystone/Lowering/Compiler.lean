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
  | .loadTable id address => compileExpr address ++ [.loadTable id]
  | .loadCache id address => compileExpr address ++ [.loadCache id]
  | .store address value => compileExpr address ++ compileExpr value ++ [.store]
  | .whenLt lhs rhs body =>
    compileExpr lhs ++ compileExpr rhs ++ [.enterMask] ++ compile body ++ [.leaveMask]

end Keystone.Lowering
