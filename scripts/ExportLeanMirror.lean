import Papers.Rockel2026ExactBlest.ArticlePresentation

open Papers.Rockel2026ExactBlest.ArticleBridge

/-- This module imports the checked certificate before producing any output. -/
def main (args : List String) : IO Unit := do
  let [destination, jsonDestination] := args
    | throw (IO.userError "usage: lake env lean --run scripts/ExportLeanMirror.lean OUTPUT.tex OUTPUT.json")
  let .ok tex := latexDocument | throw (IO.userError "invalid definition closure")
  let .ok report := certificateReport | throw (IO.userError "invalid certificate report")
  let .ok companion := companionJson | throw (IO.userError "invalid mathematical companion")
  IO.FS.writeFile destination tex
  IO.FS.writeFile jsonDestination (companion.pretty ++ "\n")
  IO.println report
