/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Mathlib.Tactic
open Lean

/-- Expand the unchanged envelope comparison for an old-count rectangle. -/
macro "return_old " hd:term "," hp:term " using " positive:term " at_branch " br:term : tactic => do
  let delta := mkIdent `δ
  let amp := mkIdent `p
  let old := mkIdent `finiteEnvelope_le_old
  let pos := mkIdent `countJ_pos
  let finish := mkIdent `exponent_lt_of_margin
  `(tactic| (
    have hd0 : $delta ∈ Set.Icc 0 (3/4 : ℝ) := by
      constructor <;> linarith [($hd).1,($hd).2]
    have hp0 : $amp ∈ Set.Icc 0 (1/2 : ℝ) := by
      constructor <;> linarith [($hp).1,($hp).2]
    have hR := $old hd0 hp0
    exact $finish ($pos $br hd0 hp0) ($positive $hd $hp) hR))

/-- Expand the unchanged window comparison for one certified rectangle. -/
macro "return_window " hd:term "," hp:term " using " positive:term " at_branch " br:term
  " at_window " w:term " with_member " hw:term
  " box(" a:term "," b:term "," c:term "," d:term ")" : tactic => do
  let delta := mkIdent `δ
  let amp := mkIdent `p
  let wBound := mkIdent `finiteEnvelope_le_window
  let pos := mkIdent `countJ_pos
  let finish := mkIdent `exponent_lt_of_margin
  let kappa := mkIdent `kappa
  `(tactic| (
    have hd0 : $delta ∈ Set.Icc 0 (3/4 : ℝ) := by
      constructor <;> linarith [($hd).1,($hd).2]
    have hp0 : $amp ∈ Set.Icc 0 (1/2 : ℝ) := by
      constructor <;> linarith [($hp).1,($hp).2]
    have ha : ($w).Available $delta $amp := by
      change $delta ∈ Set.Icc $a $b ∧ $amp ∈ Set.Icc $c $d
      constructor <;> constructor <;> linarith [($hd).1,($hd).2,($hp).1,($hp).2]
    have hR := $wBound $w $hw (κ := $kappa) ha
    exact $finish ($pos $br hd0 hp0) ($positive $hd $hp) hR))

/-- One exact guillotine-cover node; the child theorem types check the cut. -/
macro "return_split " name:ident " edge_at " e:term
  " box(" a:term "," b:term "," c:term "," d:term ")"
  " along " axis:ident " cut_at " k:term
  " left_from " lterm:term " right_from " rterm:term : command => do
  let target := mkIdent `ReturnAt
  if axis.getId == `δ then
    `(command| theorem $name {δ p : ℝ} (hδ : δ ∈ Set.Icc $a $b)
        (hp : p ∈ Set.Icc $c $d) : $target $e δ p := by
      rcases le_total δ $k with hsplit | hsplit
      · exact $lterm ⟨hδ.1,hsplit⟩ hp
      · exact $rterm ⟨hsplit,hδ.2⟩ hp)
  else if axis.getId == `p then
    `(command| theorem $name {δ p : ℝ} (hδ : δ ∈ Set.Icc $a $b)
        (hp : p ∈ Set.Icc $c $d) : $target $e δ p := by
      rcases le_total p $k with hsplit | hsplit
      · exact $lterm hδ ⟨hp.1,hsplit⟩
      · exact $rterm hδ ⟨hsplit,hp.2⟩)
  else Macro.throwErrorAt axis "cover axis must be δ or p"
