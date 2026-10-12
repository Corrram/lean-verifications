import Papers.Rockel2026ExactBlest.ArticleDocument

open Papers.Rockel2026ExactBlest.ArticleProof

/-- This module imports the checked certificate before producing any output. -/
def main (args : List String) : IO Unit := do
  let [jsonDestination] := args
    | throw (IO.userError "usage: lake env lean --run scripts/ExportLeanMirror.lean OUTPUT.json")
  let .ok companion := fullCompanionJson | throw (IO.userError "invalid mathematical companion")
  IO.FS.writeFile jsonDestination (companion.pretty ++ "\n")
  IO.println "Corollary 3.2: audited proof tree, all equality cases and support graphs."
