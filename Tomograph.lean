/- A tool for analysing Lean source code. -/
import Pantograph.Frontend
import Pantograph.Library

open Lean

namespace Pantograph

def fail (s : String) : IO UInt32 := do
  IO.eprintln s
  return 2

def dissect (args : List String) : IO UInt32 := do
  let fileName :: _args := args | fail s!"Must supply a file name"
  let file ← IO.FS.readFile fileName
  let (context, state) ← do Frontend.createContextStateFromFile file fileName (env? := .none) {}
  let frontendM: Frontend.FrontendM _ :=
    Frontend.mapCompilationSteps λ step => do
      IO.println s!"🐈 {step.stx.getKind.toString}"
      for (tree, i) in step.trees.zipIdx do
        IO.println s!"🌲[{i}] {← tree.toString}"
      for (msg, i) in step.msgs.zipIdx do
        IO.println s!"🔈[{i}] {← msg.toString}"
  let (_, _) ← frontendM.run {} |>.run context |>.run state
  return 0

end Pantograph

open Pantograph

def help : IO UInt32 := do
  IO.println "Usage: tomograph dissect FILE_NAME"
  return 1

def main (args : List String) : IO UInt32 := do
  let command :: args := args | help
  unsafe do
    Pantograph.initSearch ""
  match command with
  | "dissect" => dissect args
  | _ => fail s!"Unknown command {command}"
