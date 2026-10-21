import Keystone.Lowering.Gather

open Keystone Keystone.Lowering
namespace MutationTests

private def cfg : GPU.Config := ⟨5, 2, 8⟩
private def input : GPU.Input := ⟨#[2, 0, 1], #[10, 11, 20, 21, 30, 31]⟩
private def activeLane : Context := gatherContext cfg input 1
private def paddedLane : Context := gatherContext cfg input 5

#guard GPU.validateInput cfg input
#guard GPU.reference cfg input == #[30, 31, 10, 11, 20]
#guard match source gather activeLane {} with
  | .ok state => state.output 1 == GPU.referenceAt cfg input 1
  | _ => false
#guard match source gather paddedLane {} with
  | .ok state => state.trace.isEmpty
  | _ => false

-- Mutate kernel syntax; keep the interpreters and gather specification fixed.
private def missingGuard : Cmd :=
  match gather with
  | .whenLt _ _ body => body
  | other => other

private def wrongPage : Cmd :=
  match gather with
  | .whenLt lhs rhs (.seq (.set id (.bin .div a b)) rest) =>
      .whenLt lhs rhs (.seq (.set id (.bin .mod a b)) rest)
  | other => other

#guard match source missingGuard paddedLane {} with
  | .error (.outOfBounds .output 5, _) => true
  | _ => false
#guard match source wrongPage activeLane {} with
  | .ok state => state.output 1 == 11 && state.output 1 != GPU.referenceAt cfg input 1
  | _ => false

-- Correct compilation preserves the bug in a broken source kernel.
#guard match target (compile missingGuard) paddedLane ⟨{}, [], true, []⟩ with
  | .error (.outOfBounds .output 5, _) => true
  | _ => false
#guard match target (compile wrongPage) activeLane ⟨{}, [], true, []⟩ with
  | .ok machine => machine.state.output 1 == 11
  | _ => false

-- Corrupt copies of compiled code; these are no longer `compile gather`.
private def missingMasks := (compile gather).filter fun i => i != .enterMask && i != .leaveMask
private def wrongDivision := (compile gather).map fun i => if i == .bin .div then .bin .mod else i

#guard match target missingMasks paddedLane ⟨{}, [], true, []⟩ with
  | .error (.outOfBounds .output 5, _) => true
  | _ => false
#guard match target wrongDivision activeLane ⟨{}, [], true, []⟩ with
  | .ok machine => machine.state.output 1 != GPU.referenceAt cfg input 1
  | _ => false

-- A missing predicate restore can suppress a subsequent store.
private def guardedStore : Cmd :=
  .seq (.whenLt (.lit 1) (.lit 0) .skip) (.store (.lit 0) (.lit 7))
private def missingRestore := (compile guardedStore).filter (· != .leaveMask)

#guard match source guardedStore activeLane {} with
  | .ok state => state.output 0 == 7
  | _ => false
#guard match target missingRestore activeLane ⟨{}, [], true, []⟩ with
  | .ok machine => machine.state.output 0 == 0 && !machine.active
  | _ => false

-- Equal output/trace alone can miss a leaked predicate frame.
private def emptyGuard : Cmd := .whenLt (.lit 0) (.lit 1) .skip
#guard match target (compile emptyGuard) activeLane ⟨{}, [], true, []⟩,
    target ((compile emptyGuard).filter (· != .leaveMask)) activeLane ⟨{}, [], true, []⟩ with
  | .ok good, .ok bad => good.state.output 0 == bad.state.output 0 &&
      good.state.trace == bad.state.trace && good.masks.isEmpty && bad.masks == [true]
  | _, _ => false

end MutationTests
