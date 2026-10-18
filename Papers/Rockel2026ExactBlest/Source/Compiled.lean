import LeanMirror.Tex.Meta

/-! # The article, compiled by the kernel

`compiled : compileArticle source = some doc` is checked by the kernel from the
contents of `article.tex`. The last argument pins those contents: after editing
the article, update it (the error message, or `tex_diagnostics.py --pin`, gives
the new value) so that Lake recompiles the article. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#mirror_article Papers.Rockel2026ExactBlest.Source "article.tex" "fnv1a64:f07baff0c28f2ac7"
