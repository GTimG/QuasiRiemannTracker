/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Submissions.hailey_collet_1252270103.Record12518109.Bernstein
import Mathlib.Tactic
open Lean

/-- This command emits the same coefficient, identity and positivity
statements as the expanded return certificates, with no external evaluator. -/
macro "positive_poly " name:ident " dims(" m:term "," n:term ") " f:term
 " via " expansion:ident " margin " margin:term " box(" a:term "," b:term "," c:term "," d:term ")"
 " coefficients " table:term : command => do
 let base := name.getId.eraseMacroScopes.toString
 let coeff := mkIdent (Name.mkSimple (base++"_coefficients"))
 let identity := mkIdent (Name.mkSimple (base++"_identity"))
 let positive := mkIdent (Name.mkSimple (base++"_pos"))
 let expName := expansion.getId.eraseMacroScopes.toString
 let poly := mkIdent (Name.mkSimple (String.ofList (expName.toList.take (expName.length-9))))
 let c1 ← `(command| noncomputable def $coeff : Fin ($m+1) → Fin ($n+1) → ℝ := $table)
 let c2 ← `(command|
   theorem $identity (δ p : ℝ) : ($f) δ p =
     Record12518109.Bernstein.bsum $m $n $margin $coeff $a $b $c $d δ p := by
     dsimp only
     rw [$expansion:term]
     norm_num [Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,
       $coeff:term,Fin.sum_univ_succ,$poly:term] <;> ring)
 let c3 ← `(command|
   theorem $positive {δ p : ℝ} (hδ : δ ∈ Set.Icc $a $b) (hp : p ∈ Set.Icc $c $d) :
     0 < ($f) δ p := by
     rw [$identity:term]
     apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
     intro i j
     fin_cases i <;> fin_cases j <;> norm_num [$coeff:term])
 return ⟨mkNullNode #[c1.raw,c2.raw,c3.raw]⟩
