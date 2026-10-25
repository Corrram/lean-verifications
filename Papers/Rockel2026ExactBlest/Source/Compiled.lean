import Proofread.Meta
import Proofread.Library.UnitSquare
import Papers.Rockel2026ExactBlest.Source.LexCache

/-! # The article, compiled by the kernel

`compiled : compileArticle vocab source = some doc` is checked by the kernel from
the contents of `article.tex`, with the core vocabulary and the vocabulary of
probability on the unit square. The pin (the last string) is the hash of the
article. After editing the article, run

    lake exe proofread prepare article.tex --lean Compiled.lean --cache LexCache \
      --module Papers.Rockel2026ExactBlest.Source.LexCache

in this folder: it updates the pin, so that Lake recompiles the article, and
writes the lexing certificates of the changed sections (`LexCache/`, one module
per section, named after its content), so that only those are relexed. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_article Papers.Rockel2026ExactBlest.Source "article.tex" "fnv1a64:9783c81c5bde7e10" with Proofread.UnitSquare.withCore
