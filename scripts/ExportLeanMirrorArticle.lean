import Papers.Rockel2026ExactBlest.ArticleIndex

def main (args : List String) : IO Unit := do
  let [destination] := args
    | throw (IO.userError "usage: ExportLeanMirrorArticle.lean OUTPUT.json")
  IO.FS.writeFile destination
    ((Lean.Json.mkObj [
      ("evidence", Papers.Rockel2026ExactBlest.ArticleIndex.evidence),
      ("documents", Papers.Rockel2026ExactBlest.ArticleCalculations.documents)
    ]).pretty ++ "\n")
