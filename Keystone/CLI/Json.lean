import Lean.Data.Json

namespace Keystone.CLI
open Lean

def object (json : Json) (required : List String) (optional : List String := []) : Except String Unit := do
  let fields ← json.getObj?
  for key in required do
    let _ ← json.getObjVal? key
  for (key, _) in fields.toList do
    unless key ∈ required ++ optional do throw s!"unknown field: {key}"

def field (json : Json) (key : String) : Except String Json := json.getObjVal? key
def nat (json : Json) (key : String) : Except String Nat := do (← field json key).getNat?
def string (json : Json) (key : String) : Except String String := do (← field json key).getStr?
def array (json : Json) (key : String) : Except String (Array Json) := do (← field json key).getArr?

def optional (json : Json) (key : String) : Option Json := (json.getObjVal? key).toOption

/-- One request per process. Parsing and native compilation are outside the proofs. -/
def serve (handler : Json → Except String Json) : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  let (output, code) : Json × UInt32 := match Json.parse input >>= handler with
    | .ok result => (result, 0)
    | .error message => (Json.mkObj [("status", toJson "invalid_input"),
                                    ("error", toJson message)], 2)
  (← IO.getStdout).putStrLn output.compress
  return code

end Keystone.CLI
