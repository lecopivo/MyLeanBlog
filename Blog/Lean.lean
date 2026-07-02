import VersoBlog

open Lean Elab
open Verso ArgParse Doc Elab

namespace Verso.Genre.Blog

/-- Marker name for Manual-style Lean snippets in blog posts. -/
def «lean'» : Unit := ()

def leanPrimeContextName : Name := `leanPrime

def leanPrimeContextIdent : Ident := mkIdent leanPrimeContextName

def ensureLeanPrimeContext : DocElabM Unit := do
  if (exampleContextExt.getState (← getEnv)).contexts.contains leanPrimeContextName then
    return ()
  let context := Parser.mkInputContext "" (← getFileName)
  let (_header, state, _msgs) ← Parser.parseHeader context
  let commandState := Command.mkState (← getEnv) {}
  let commandState := { commandState with
    infoState := { enabled := true },
    scopes := [{ header := "", opts := pp.tagAppFns.set {} true }]
  }
  modifyEnv fun env =>
    exampleContextExt.modifyState env fun s =>
      { s with contexts := s.contexts.insert leanPrimeContextName (.inline commandState state) }

structure LeanPrimeBlockConfig where
  «show» : Bool
  keep : Bool
  name : Option Name := none
  error : Bool
  showProofStates : Bool

instance [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : FromArgs LeanPrimeBlockConfig m where
  fromArgs :=
    LeanPrimeBlockConfig.mk <$>
      .flag `show true "Include in rendered page?" <*>
      .flag `keep true "Keep environment changes from this block?" <*>
      .named `name .name true <*>
      .flag `error false "Error expected in code?" <*>
      .flag `showProofStates true "Show proof states in rendered page?"

@[code_block «lean'»]
def leanPrimeBlock : CodeBlockExpanderOf LeanPrimeBlockConfig := fun config str => do
  ensureLeanPrimeContext
  lean {
    exampleContext := leanPrimeContextIdent,
    «show» := config.show,
    keep := config.keep,
    name := config.name,
    error := config.error,
    showProofStates := config.showProofStates
  } str

structure LeanPrimeInlineConfig where
  type : Option StrLit
  universes : Option StrLit

instance [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] : FromArgs LeanPrimeInlineConfig m where
  fromArgs := LeanPrimeInlineConfig.mk <$> .named `type strLit true <*> .named `universes strLit true
where
  strLit : ValDesc m StrLit := {
    description := "string literal containing an expected type",
    signature := .String,
    get
      | .str s => pure s
      | other => throwError "Expected string, got {repr other}"
  }

@[role «lean'»]
def leanPrimeRole : RoleExpanderOf LeanPrimeInlineConfig := fun config inlines => do
  ensureLeanPrimeContext
  leanCanonical {
    exampleContext := leanPrimeContextIdent,
    type := config.type,
    universes := config.universes
  } inlines

end Verso.Genre.Blog
