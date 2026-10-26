/- The first point of an interval at which a function is nonnegative, its enclosure from a sign
certificate on each side, and the root equation where the function is continuous and increasing.
Released under Apache 2.0. -/
import Candidate.Cycle63.Certificate.Bracket
import Candidate.Cycle63.Certificate.MonoTactic

set_option autoImplicit false

namespace Cycle63.Certificate

/-- The smallest point of `[a, b]` at which `f` is nonnegative (the infimum of those points). -/
noncomputable def firstNonneg (f : ℝ → ℝ) (a b : ℝ) : ℝ := sInf {q ∈ Set.Icc a b | 0 ≤ f q}

/-- If `f` is negative on `[a, c]`, strictly increasing and continuous on `[c, c₂]`, negative at a
point `c₁` of `(c, c₂)` and positive at `c₂ ≤ b`, the first point of `[a, b]` at which `f` is
nonnegative is a root of `f` in `(c₁, c₂)`. -/
theorem firstNonneg_root {f : ℝ → ℝ} {a b c c₁ c₂ : ℝ} (hac : a ≤ c) (hcc₁ : c < c₁)
    (hc₁c₂ : c₁ < c₂) (hc₂b : c₂ ≤ b) (hfar : ∀ q ∈ Set.Icc a c, f q < 0)
    (hmono : StrictMonoOn f (Set.Icc c c₂)) (hcont : ContinuousOn f (Set.Icc c c₂))
    (hlo : f c₁ < 0) (hhi : 0 < f c₂) :
    f (firstNonneg f a b) = 0 ∧ c₁ < firstNonneg f a b ∧ firstNonneg f a b < c₂ := by
  obtain ⟨r, ⟨hr₁, hr₂⟩, hr⟩ := intermediate_value_Ioo hc₁c₂.le
    (hcont.mono (Set.Icc_subset_Icc hcc₁.le le_rfl)) ⟨hlo, hhi⟩
  have hmem : r ∈ {q ∈ Set.Icc a b | 0 ≤ f q} :=
    ⟨⟨by linarith, by linarith⟩, hr.ge⟩
  have hbdd : BddBelow {q ∈ Set.Icc a b | 0 ≤ f q} := ⟨a, fun q hq => hq.1.1⟩
  have heq : firstNonneg f a b = r := by
    refine le_antisymm (csInf_le hbdd hmem) (le_csInf ⟨r, hmem⟩ fun q hq => ?_)
    by_contra hlt
    push Not at hlt
    rcases le_or_gt q c with hle | hgt
    · exact absurd hq.2 (not_le.mpr (hfar q ⟨hq.1.1, hle⟩))
    · have := hmono ⟨hgt.le, by linarith⟩ ⟨by linarith, hr₂.le⟩ hlt
      rw [hr] at this
      exact absurd hq.2 (not_le.mpr this)
  rw [heq]
  exact ⟨hr, hr₁, hr₂⟩

/-- If `f` is strictly increasing and continuous on `[a, b]`, negative at `c₁ > a` and positive at
`c₂ ≤ b`, the first point of `[a, b]` at which `f` is nonnegative is a root of `f` in `(c₁, c₂)`. -/
theorem firstNonneg_root_of_strictMonoOn {f : ℝ → ℝ} {a b c₁ c₂ : ℝ} (hac₁ : a < c₁)
    (hc₁c₂ : c₁ < c₂) (hc₂b : c₂ ≤ b) (hmono : StrictMonoOn f (Set.Icc a b))
    (hcont : ContinuousOn f (Set.Icc a b)) (hlo : f c₁ < 0) (hhi : 0 < f c₂) :
    f (firstNonneg f a b) = 0 ∧ c₁ < firstNonneg f a b ∧ firstNonneg f a b < c₂ := by
  have hsub : Set.Icc a c₂ ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hc₂b
  refine firstNonneg_root le_rfl hac₁ hc₁c₂ hc₂b (fun q hq => ?_) (hmono.mono hsub)
    (hcont.mono hsub) hlo hhi
  obtain rfl : q = a := le_antisymm hq.2 hq.1
  exact (hmono ⟨le_rfl, by linarith⟩ ⟨hac₁.le, by linarith⟩ hac₁).trans hlo

open Lean Meta Elab Command Term

/-- The sign of an interval: `1` if it lies above zero, `-1` if below, `0` if it contains zero. -/
def intervalSign (I : QInterval) : Int :=
  if 0 < I.lo then 1 else if I.hi < 0 then -1 else 0

/-- Options of `bracket_root`: decimal digits of the bracket and bisection depth of the certificate. -/
declare_syntax_cat bracketRootOption
syntax " (" &"digits" " := " num ")" : bracketRootOption
syntax " (" &"depth" " := " num ")" : bracketRootOption

/-- `bracket_root name : f on a b using [h₁, …] unfolding [c₁, …]` proves
`name : (c₁ ≤ x ∧ x ≤ c₂) ∧ f x = 0` for `x = firstNonneg f a b` and a function `f : ℝ → ℝ` that is
negative at `a` and positive at `b`, where `f t`, after unfolding the constants `cᵢ` (every
definition with `unfolding *`), is a rational
expression in `t` and the atoms bounded by the hypotheses `hⱼ`. The bracket `[c₁, c₂]` is found at
elaboration time by bisection with the interval evaluation of `CExpr.enclose`, rounded outward to `d`
decimal digits (default 12). The proof splits `[a, c₁]` at the point `c` that lies a 256th of
`[a, b]` below `c₁`: `rat_pos` shows `f < 0` on `[a, c]` (bisection depth `k`, default 30),
`rat_mono` shows that `f` is continuous and increases on `[c, c₂]`, and `rat_pos` (or `norm_num`
when `f` has no atoms) shows `f c₁ < 0 < f c₂`. With `by hf`, for a proof `hf` that `f` is strictly
increasing and continuous on `[a, b]`, only the signs at `c₁` and `c₂` are certified. -/
syntax (name := bracketRootCmd) (docComment)? "bracket_root " ident (bracketRootOption)* " : " term
  " on " term:max term:max (" by " term:max)? (" using " "[" term,* "]")? " unfolding " bracketUnfolds :
  command

@[command_elab bracketRootCmd] def elabBracketRoot : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs = 0 then none else some ⟨stx[0][0]⟩
  let name : Ident := ⟨stx[2]⟩
  let f : Term := ⟨stx[5]⟩
  let aStx : Term := ⟨stx[7]⟩
  let bStx : Term := ⟨stx[8]⟩
  let mono? : Option Term := if stx[9].getNumArgs = 0 then none else some ⟨stx[9][1]⟩
  let hyps : Array Term := if stx[10].getNumArgs = 0 then #[] else stx[10][2].getSepArgs.map (⟨·⟩)
  let (unfoldNames, all) ← readUnfolds stx[12]
  let mut digits : ℕ := 12
  let mut depth : ℕ := 30
  for option in stx[3].getArgs do
    let value ← match option[3].isNatLit? with
      | some v => pure v
      | none => throwError "bracket_root: option {option} has no numeral value"
    match option[1].getAtomVal with
    | "digits" => digits := value
    | "depth" => depth := value
    | other => throwError "bracket_root: unknown option {other}"
  let (lo, hi, split, unfolded) ← liftTermElabM do
    let spec ← Unfolding.mk' unfoldNames all
    let mut atoms : Array Expr := #[]
    let mut boxes : Array Expr := #[]
    for h in hyps do
      let he ← elabTerm h none
      synthesizeSyntheticMVarsNoPostponing
      let (v, vlo, vhi) ← atomOfBound (← inferType he)
      atoms := atoms.push v
      boxes := boxes.push (mkApp2 (mkConst ``QInterval.mk) (← mkRatLit vlo) (← mkRatLit vhi))
    let fe ← elabTerm f (some (← mkArrow (mkConst ``Real) (mkConst ``Real)))
    synthesizeSyntheticMVarsNoPostponing
    let fe ← instantiateMVars fe
    let a ← ratOfExpr (← elabTerm aStx (some (mkConst ``Real)))
    let b ← ratOfExpr (← elabTerm bStx (some (mkConst ``Real)))
    -- `f t` as a `CExpr` once, with `t` the variable `0`; the atoms follow it.
    let ce ← withLocalDeclD `t (mkConst ``Real) fun t =>
      reifyBracket (#[t] ++ atoms) spec (mkApp fe t).headBeta
    -- The value of `f` at a rational point, as an interval, with the atoms at their boxes.
    let signAt (p : ℚ) : TermElabM Int := do
      let pr ← mkRatLit p
      let box ← mkListLit (mkConst ``QInterval)
        (mkApp2 (mkConst ``QInterval.mk) pr pr :: boxes.toList)
      match ← enclose 64 box ce with
      | some I => return intervalSign I
      | none => return 0
    unless (← signAt a) = -1 do throwError "bracket_root: f is not certified negative at {a}"
    unless (← signAt b) = 1 do throwError "bracket_root: f is not certified positive at {b}"
    -- Bisection keeps `f lo < 0`; a midpoint whose sign is not certified negative moves `hi`.
    let mut lo := a
    let mut hi := b
    for _ in [0:4 * digits + 8] do
      let m := (lo + hi) / 2
      if (← signAt m) = -1 then lo := m else hi := m
    -- Round outward and step by one unit of the last digit until both signs are certified.
    let unit : ℚ := 1 / 10 ^ digits
    let mut c₁ := decimalDown digits lo
    let mut c₂ := decimalUp digits hi
    for _ in [0:8] do
      if (← signAt c₁) = -1 then break
      c₁ := c₁ - unit
    for _ in [0:8] do
      if (← signAt c₂) = 1 then break
      c₂ := c₂ + unit
    unless a < c₁ ∧ (← signAt c₁) = -1 ∧ (← signAt c₂) = 1 ∧ c₂ ≤ b do
      throwError "bracket_root: no certified sign change found at {digits} digits"
    let c := decimalDown (digits + 3) (c₁ - (b - a) / 256)
    unless a < c do throwError "bracket_root: the root is too close to {a}"
    return (c₁, c₂, c, ← spec.lemmas)
  let realTy ← `(ℝ)
  let loReal ← liftMacroM <| rationalSyntax lo realTy
  let hiReal ← liftMacroM <| rationalSyntax hi realTy
  let splitReal ← liftMacroM <| rationalSyntax split realTy
  let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    unfolded.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let depthLit := Syntax.mkNumLit (toString depth)
  -- The signs at the two ends of the bracket: by exact evaluation when `f` has no atoms.
  let pointSign ← if hyps.isEmpty then `(tactic| norm_num) else `(tactic| rat_pos [$hyps,*])
  if let some hf := mono? then
    elabCommand (← `(command|
      $[$doc?:docComment]? theorem $name :
          ($loReal ≤ Cycle63.Certificate.firstNonneg $f $aStx $bStx ∧
            Cycle63.Certificate.firstNonneg $f $aStx $bStx ≤ $hiReal) ∧
            $f (Cycle63.Certificate.firstNonneg $f $aStx $bStx) = 0 := by
        have hm := $hf
        have hlo : $f $loReal < 0 := by
          simp only [$lemmas,*]
          $pointSign:tactic
        have hhi : 0 < $f $hiReal := by
          simp only [$lemmas,*]
          $pointSign:tactic
        obtain ⟨hroot, hgt, hlt⟩ := Cycle63.Certificate.firstNonneg_root_of_strictMonoOn
          (f := $f) (a := $aStx) (b := $bStx) (by norm_num) (by norm_num) (by norm_num) hm.1 hm.2
          hlo hhi
        exact ⟨⟨hgt.le, hlt.le⟩, hroot⟩))
    return
  elabCommand (← `(command|
    $[$doc?:docComment]? theorem $name :
        ($loReal ≤ Cycle63.Certificate.firstNonneg $f $aStx $bStx ∧
          Cycle63.Certificate.firstNonneg $f $aStx $bStx ≤ $hiReal) ∧
          $f (Cycle63.Certificate.firstNonneg $f $aStx $bStx) = 0 := by
      have hfar : ∀ q ∈ Set.Icc ($aStx : ℝ) $splitReal, $f q < 0 := fun q hq => by
        simp only [$lemmas,*]
        rat_pos (depth := $depthLit) [hq, $hyps,*]
      have hmono : StrictMonoOn (fun t => $f t) (Set.Icc $splitReal $hiReal) ∧
          ContinuousOn (fun t => $f t) (Set.Icc $splitReal $hiReal) := by
        simp only [$lemmas,*]
        rat_mono (depth := $depthLit) [$hyps,*]
      have hlo : $f $loReal < 0 := by
        simp only [$lemmas,*]
        $pointSign:tactic
      have hhi : 0 < $f $hiReal := by
        simp only [$lemmas,*]
        $pointSign:tactic
      obtain ⟨hroot, hgt, hlt⟩ := Cycle63.Certificate.firstNonneg_root (f := $f) (a := $aStx)
        (b := $bStx) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hfar hmono.1 hmono.2
        hlo hhi
      exact ⟨⟨hgt.le, hlt.le⟩, hroot⟩))

end Cycle63.Certificate
