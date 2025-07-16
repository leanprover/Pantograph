import Pantograph.Frontend.Basic

open Lean

namespace Pantograph.Frontend

structure SearchUnit where
  trees : List Elab.InfoTree

namespace Refactor

structure Context where

structure State where
  units : List SearchUnit

abbrev RefactorM := ReaderT Context $ StateRefT State FrontendM

end Refactor

export Refactor (RefactorM)

def preprocessRefactor : RefactorM Unit := executeFrontend λ step => do
  sorry

end Pantograph.Frontend
