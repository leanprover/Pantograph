import Lean
open Lean

namespace Pantograph

-- Functions for creating contexts and states
@[export pantograph_default_elab_context]
def defaultElabContext: Elab.Term.Context := {
    declName? := .some `mystery,
    errToSorry := false,
  }

/-- Read syntax object from string -/
def parseTerm (env: Environment) (s: String): Except String Syntax :=
  Parser.runParserCategory
    (env := env)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")

def parseTermM [Monad m] [MonadEnv m] (s: String): m (Except String Syntax) := do
  return Parser.runParserCategory
    (env := ← MonadEnv.getEnv)
    (catName := `term)
    (input := s)
    (fileName := "<stdin>")

/-- Parse a syntax object. May generate additional metavariables! -/
def elabType (syn: Syntax): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabType syn
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)
def elabTerm (syn: Syntax) (expectedType? : Option Expr := .none): Elab.TermElabM (Except String Expr) := do
  try
    let expr ← Elab.Term.elabTerm (stx := syn) expectedType?
    return .ok expr
  catch ex => return .error (← ex.toMessageData.toString)

open Parser in
def runParserCategory' (env : Environment) (catName : Name) (input : String) (fileName := "<input>") : Except String (Syntax × String.Pos) :=
  let p := andthenFn whitespace (categoryParserFnImpl catName)
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if s.allErrors.isEmpty  then
    Except.ok (s.stxStack.back, s.pos)
  else
    Except.error (s.toErrorMsg ictx)

end Pantograph
