import Lean

/-! # Fail-closed checks for theorems advertised as verified

`#assert_standard_axioms` accepts only a theorem declaration whose transitive
axioms are among Lean's three standard foundational axioms. In particular,
`sorryAx`, user axioms, and `Lean.ofReduceBool` are rejected.
-/

open Lean Elab Command

elab "#assert_standard_axioms " decl:ident : command => do
  let name := decl.getId
  let env ← getEnv
  match env.find? name with
  | some (.thmInfo _) => pure ()
  | some _ => throwErrorAt decl "{name} is not a theorem declaration"
  | none => throwErrorAt decl "unknown theorem {name}"
  let axioms ← collectAxioms name
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwErrorAt decl "{name} depends on nonstandard axiom {axiomName}"

