import Lean.Parser
import Lean.Elab.Frontend

open Lean

namespace Lean.FileMap

/-- Extract the range of a `Syntax` expressed as lines and columns. -/
@[export pantograph_frontend_stx_range]
protected def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)

end Lean.FileMap
namespace Lean.PersistentArray

/--
Drop the first `n` elements of a `PersistentArray`, returning the results as a `List`.

We can't remove the `[Inhabited α]` hypotheses here until
`PersistentArray`'s `GetElem` instance also does.
-/
protected def drop [Inhabited α] (t : PersistentArray α) (n : Nat) : List α :=
  List.range (t.size - n) |>.map fun i => t.get! (n + i)

end Lean.PersistentArray

namespace Pantograph.Frontend

@[export pantograph_frontend_stx_byte_range]
def stxByteRange (stx : Syntax) : String.Pos.Raw × String.Pos.Raw :=
  let pos := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD 0
  (pos, endPos)

structure Context where
  cancelTk? : Option IO.CancelToken := .none

/-- This `FrontendM` comes with more options. -/
abbrev FrontendM := ReaderT Context Elab.Frontend.FrontendM

structure CompilationStep where
  scope : Elab.Command.Scope
  fileName : String
  fileMap : FileMap
  src : Substring.Raw
  stx : Syntax
  before : Environment
  after : Environment
  msgs : List Message
  trees : List Elab.InfoTree

@[export pantograph_frontend_compilation_step_defined_constants_m]
protected def CompilationStep.newConstants (step : CompilationStep) : IO NameSet := do
  step.after.constants.map₂.foldlM (init := .empty) λ acc name _ => do
    if step.before.contains name then
      return acc
    let coreM : CoreM Bool := Option.isSome <$> findDeclarationRanges? name
    let hasRange ← coreM.run'
      { fileName := step.fileName, fileMap := step.fileMap }
      { env := step.after }
      |>.toBaseIO
    match hasRange with
    | .ok true => return acc.insert name
    | .ok false => return acc
    | .error e => throw $ IO.userError (← e.toMessageData.toString)

/-- Like `Elab.Frontend.runCommandElabM`, but taking `cancelTk?` into account. -/
@[inline] def runCommandElabM (x : Elab.Command.CommandElabM α) : FrontendM α := do
  let config ← read
  let ctx ← readThe Elab.Frontend.Context
  let s ← get
  let cmdCtx : Elab.Command.Context := {
    cmdPos       := s.cmdPos
    fileName     := ctx.inputCtx.fileName
    fileMap      := ctx.inputCtx.fileMap
    snap?        := none
    cancelTk?    := config.cancelTk?
  }
  match (← liftM <| EIO.toIO' <| (x cmdCtx).run s.commandState) with
  | Except.error e      => throw <| IO.Error.userError s!"unexpected internal error: {← e.toMessageData.toString}"
  | Except.ok (a, sNew) => Elab.Frontend.setCommandState sNew; return a

def elabCommandAtFrontend (stx : Syntax) : FrontendM Unit := do
  runCommandElabM do
    let initMsgs ← modifyGet λ st =>
      (st.messages, { st with messages := {} })
    Elab.Command.elabCommandTopLevel stx
    modify λ state => { state with
      messages := initMsgs ++ state.messages }

open Elab.Frontend in
def processCommand : FrontendM Bool := do
  updateCmdPos
  let cmdState ← getCommandState
  let ictx ← getInputContext
  let pstate ← getParserState
  let scope := cmdState.scopes.head!
  let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  match profileit "parsing" scope.opts fun _ => Parser.parseCommand ictx pmctx pstate cmdState.messages with
  | (cmd, ps, messages) =>
    modify fun s => { s with commands := s.commands.push cmd }
    setParserState ps
    setMessages messages
    elabCommandAtFrontend cmd
    pure (Parser.isTerminalCommand cmd)

/--
Process one command, returning a `CompilationStep` and
`done : Bool`, indicating whether this was the last command.
-/
@[export pantograph_frontend_process_one_command_m]
def processOneCommand: FrontendM (CompilationStep × Bool) := do
  let s := (← get).commandState
  let before := s.env
  let done ← processCommand
  let stx := (← get).commands.back!
  let src := (← readThe Elab.Frontend.Context).inputCtx.substring
    (← get).cmdPos
    (← get).parserState.pos
  let s' := (← get).commandState
  let after := s'.env
  let msgs := s'.messages.toList.drop s.messages.toList.length
  let trees := s'.infoState.trees.toList
  let { fileName, fileMap, .. }  := (← readThe Elab.Frontend.Context).inputCtx
  return ({ scope := s.scopes.head!, fileName, fileMap, src, stx, before, after, msgs, trees }, done)

/-- Executes a `FrontendM`-based monad until completion -/
partial def executeFrontend { m } [Monad m] [MonadLiftT FrontendM m]
  (f : CompilationStep → m Unit) : m Unit := do
  let (cmd, done) ← processOneCommand
  if done then
    if cmd.src.bsize == 0 then
      return ()
    else
      f cmd
  else
    f cmd
    executeFrontend f

def mapCompilationSteps { m α }
  [Monad m] [MonadLiftT FrontendM m] [MonadLiftT (ST IO.RealWorld) m]
  (f : CompilationStep → m α) : m (List α) := do
  let f' (step : CompilationStep) : StateRefT' IO.RealWorld (List α) m Unit := do
    let a ← f step
    modify (a :: ·)
  let (_, li) ← executeFrontend f' |>.run []
  return li.reverse

@[export pantograph_frontend_find_source_path_m]
def findSourcePath (module : Name) : IO System.FilePath := do
  let olean ← findOLean module
  return System.FilePath.mk (olean.toString.replace ".lake/build/lib/" "") |>.withExtension "lean"

def defaultFileName := "<anonymous>"

/--
Use with
```lean
let m: FrontendM α := ...
let (context, state) ← createContextStateFromFile ...
m.run context |>.run' state
```
-/
@[export pantograph_frontend_create_context_state_from_file_m]
def createContextStateFromFile
    (file : String) -- Content of the file
    (fileName : String := defaultFileName)
    (env? : Option Lean.Environment := .none) -- If set to true, assume there's no header.
    (opts : Options := {})
    : IO (Elab.Frontend.Context × Elab.Frontend.State) := unsafe do
  --let file ← IO.FS.readFile (← findSourcePath module)
  let inputCtx := Parser.mkInputContext file fileName

  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, parserState, messages) ← match env? with
    | .some env => pure (env, {}, .empty)
    | .none =>
      -- Only process the header if we don't have an environment.
      let (env, messages) ← Elab.processHeader header opts messages inputCtx
      pure (env, parserState, messages)
  let commandState := Elab.Command.mkState env messages opts
  let context: Elab.Frontend.Context := { inputCtx }
  let state: Elab.Frontend.State := {
    commandState := { commandState with infoState.enabled := true },
    parserState,
    cmdPos := parserState.pos
  }
  return (context, state)

/-- Returns the command state at the end of execution -/
def collectEndState : FrontendM Elab.Command.State := do
  executeFrontend λ _ => pure ()
  let state ← get
  return state.commandState
