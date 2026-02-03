import Lean.Data.Json
import Lean.Environment

import Pantograph
import Repl

-- Main IO functions
open Pantograph.Repl
open Pantograph.Protocol

/-- Print a string to stdout without buffering -/
def printImmediate (s : String) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStr (s ++ "\n")
  stdout.flush

/-- Parse a command either in `{ "cmd": ..., "payload": ... }` form or `cmd { ... }` form. -/
def parseCommand (s: String): Except String Command := do
  match s.trimAscii.startPos.get? with
  | .some '{' =>
    -- Parse in Json mode
    Lean.fromJson? (← Lean.Json.parse s)
  | .some _ =>
    -- Parse in line mode
    let offset := s.find ' '
    if offset = s.endPos then
      return { cmd := s.sliceTo offset |>.toString, payload := Lean.Json.null }
    else
      let payload ← (s.sliceFrom offset).toString |> Lean.Json.parse
      return { cmd := (s.sliceTo offset).toString, payload := payload }
  | .none =>
    throw "Command is empty"

partial def loop : MainM Unit := do repeat do
  let state ← get
  let command ← (← IO.getStdin).getLine
  -- Halt the program if empty line is given
  if command.trimAscii.isEmpty then break
  match parseCommand command with
  | .error error =>
    let error  := Lean.toJson ({ error := "command", desc := error }: InteractionError)
    -- Using `Lean.Json.compress` here to prevent newline
    printImmediate error.compress
  | .ok command =>
    try
      let ret ← execute command
      let str := match state.options.printJsonPretty with
        | true => ret.pretty
        | false => ret.compress
      printImmediate str
    catch e =>
      let message := e.toString
      let error  := Lean.toJson ({ error := "main", desc := message }: InteractionError)
      printImmediate error.compress

def main (args: List String): IO Unit := do
  -- NOTE: A more sophisticated scheme of command line argument handling is needed.
  if args == ["--version"] then do
    IO.println s!"{Pantograph.version}"
    return

  unsafe do
    Pantograph.initSearch

  -- Separate imports and options
  let (options, imports) := args.partition (·.startsWith "--")
  let coreContext ← options.map (·.drop 2 |>.toString) |>.toArray |> Pantograph.createCoreContext
  let env ← Lean.importModules
    (imports := imports.toArray.map ({ module := ·.toName }))
    (opts := {})
    (trustLevel := 1)
    (loadExts := true)
  try
    let mainM := loop.run { coreContext } |>.run' { env }
    printImmediate "ready."
    mainM
  catch ex =>
    let message := ex.toString
    let error  := Lean.toJson ({ error := "io", desc := message }: InteractionError)
    IO.println error.compress
