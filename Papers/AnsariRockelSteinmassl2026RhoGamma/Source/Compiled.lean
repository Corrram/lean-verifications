import Proofread.Meta
import Proofread.Library.UnitSquare

/-! # The article, compiled by the kernel

`compiled : compileArticle vocab source = some doc` is checked by the kernel from
the contents of `article.tex` (arXiv:2609.19890v1 with the edits in
`article-edits.diff`), with the core vocabulary and the vocabulary of
probability on the unit square. The last string pins the article's contents. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#proofread_article Papers.AnsariRockelSteinmassl2026RhoGamma.Source "article.tex" "fnv1a64:9776be422f7dabdf" with Proofread.UnitSquare.withCore
