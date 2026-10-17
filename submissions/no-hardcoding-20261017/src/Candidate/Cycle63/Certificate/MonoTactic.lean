/- The `rat_mono` tactic: proves `StrictMonoOn f (Set.Icc a b)` or `StrictAntiOn f (Set.Icc a b)`,
alone or together with `ContinuousOn f (Set.Icc a b)`, for a rational expression `f` in one variable
and parameters confined to intervals, from the kernel-evaluated test `RatExpr.monoTest` on its
fraction. Released under Apache 2.0. -/
import Candidate.Cycle63.Certificate.Derivative
import Candidate.Cycle63.Certificate.Tactic

set_option autoImplicit false

open Lean Meta Elab Tactic

namespace Cycle63.Certificate

/-- `rat_mono (depth := d) [h₁, …, hₖ]` proves a goal `StrictMonoOn (fun t => f t) (Set.Icc a b)`
or `StrictAntiOn (fun t => f t) (Set.Icc a b)`, or either of them in a conjunction with
`ContinuousOn (fun t => f t) (Set.Icc a b)`, with rational `a`, `b`, for a rational expression
`f t` in `t` and parameters `vᵢ` with hypotheses `hᵢ : vᵢ ∈ Set.Icc loᵢ hiᵢ` or
`hᵢ : loᵢ ≤ vᵢ ∧ vᵢ ≤ hiᵢ`. An end of the interval may also be one of the `vᵢ`: the segment is then
extended to the outer bound of that parameter, and the result restricted to the interval. For the
fraction `N/D` of `f`, the kernel checks on the box `[a, b] × ∏ [loᵢ, hiᵢ]` that the side
conditions and `D` have strict signs and that `N' D - N D'` (or its negative) is positive, with
bisection up to depth `d` (default 6); the mean value theorem gives the monotonicity. -/
syntax (name := ratMonoTac) "rat_mono" (ratPosOption)* " [" term,* "]" : tactic

@[tactic ratMonoTac] def evalRatMono : Tactic := fun stx => withMainContext do
  let mut depth : ℕ := 6
  for option in stx[1].getArgs do
    let value ← match option[3].isNatLit? with
      | some v => pure v
      | none => throwError "rat_mono: option {option} has no numeral value"
    match option[1].getAtomVal with
    | "depth" => depth := value
    | name => throwError "rat_mono: unknown option {name}"
  let hyps : Array (TSyntax `term) := stx[3].getSepArgs.map (⟨·⟩)
  let goal ← getMainGoal
  let gty := (← instantiateMVars (← goal.getType)).consumeMData
  -- The monotonicity goal, and the continuity goal when the goal is a conjunction.
  let (monoGoal, contGoal?) := match gty.getAppFnArgs with
    | (``And, #[m, c]) => (m.consumeMData, some c.consumeMData)
    | _ => (gty, none)
  let (increasing, f, s) ← match monoGoal.getAppFnArgs with
    | (``StrictMonoOn, #[_, _, _, _, f, s]) => pure (true, f, s)
    | (``StrictAntiOn, #[_, _, _, _, f, s]) => pure (false, f, s)
    | _ => throwError "rat_mono: the goal {gty} is not StrictMonoOn or StrictAntiOn"
  if let some c := contGoal? then
    unless c.isAppOfArity ``ContinuousOn 6 do
      throwError "rat_mono: the second part of the goal {c} is not ContinuousOn"
  let (loE, hiE) ← match s.getAppFnArgs with
    | (``Set.Icc, #[_, _, lo, hi]) => pure (lo, hi)
    | _ => throwError "rat_mono: the set {s} is not an interval Set.Icc a b"
  let mut atoms : Array Expr := #[]
  let mut bounds : Array (ℚ × ℚ) := #[]
  let mut atomHyps : Array (TSyntax `term) := #[]
  for h in hyps do
    let he ← elabTerm h none
    let (v, vlo, vhi) ← boxOfHyp (← inferType he)
    atoms := atoms.push v
    bounds := bounds.push (vlo, vhi)
    atomHyps := atomHyps.push h
  -- An end of the interval is a numeral, or a parameter whose outer bound extends the segment.
  let endOf (e : Expr) (outer : (ℚ × ℚ) → ℚ) : MetaM (ℚ × Option (TSyntax `term)) := do
    if let some q ← (try some <$> ratOfExpr e catch _ => pure none) then return (q, none)
    -- Up to definitional equality: instance arguments may differ in their proof terms.
    for i in [0:atoms.size] do
      if ← isDefEq atoms[i]! e then return (outer bounds[i]!, some atomHyps[i]!)
    throwError "rat_mono: the interval end {e} is neither a numeral nor a parameter"
  let (lo, loHyp?) ← endOf loE (·.1)
  let (hi, hiHyp?) ← endOf hiE (·.2)
  let mut boxElems : Array Expr := #[← mkAppM ``Prod.mk #[← mkRatLit lo, ← mkRatLit hi]]
  for (vlo, vhi) in bounds do
    boxElems := boxElems.push (← mkAppM ``Prod.mk #[← mkRatLit vlo, ← mkRatLit vhi])
  let ratPairTy ← mkAppM ``Prod #[mkConst ``Rat, mkConst ``Rat]
  let box ← mkListLit ratPairTy boxElems.toList
  let d := mkNatLit depth
  -- The expression of the body, the bound variable being the coordinate `0`.
  let e ← withLocalDeclD `t (mkConst ``Real) fun t => do
    let body := (mkApp f t).headBeta
    reify (#[t] ++ atoms) body
  let kParams := mkNatLit atoms.size
  let increasingE := if increasing then mkConst ``Bool.true else mkConst ``Bool.false
  let hcheck ← mkFreshExprSyntheticOpaqueMVar
    (← mkEq (mkApp5 (mkConst ``RatExpr.monoTest) kParams increasingE e box d) (mkConst ``Bool.true))
  let rest ← Tactic.run hcheck.mvarId! (evalTactic (← `(tactic| decide +kernel)))
  unless rest.isEmpty do throwError "rat_mono: the kernel check left goals"
  -- The point: coordinate `0` is updated along the segment, the others are the atoms.
  let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
  let x := mkApp (mkConst ``RatExpr.ptOfList) (← mkListLit (mkConst ``Real) (zero :: atoms.toList))
  let loR ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, ← mkRatLit lo]
  let hiR ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, ← mkRatLit hi]
  let segment ← mkAppM ``Set.Icc #[loR, hiR]
  -- The box condition along the segment.
  let hboxTy ← withLocalDeclD `t (mkConst ``Real) fun t => do
    let mem ← mkAppM ``Membership.mem #[segment, t]
    let inBox ← mkAppM ``InBox #[box, ← mkAppM ``Function.update #[x, mkNatLit 0, t]]
    mkForallFVars #[t] (← mkArrow mem inBox)
  let hbox ← mkFreshExprSyntheticOpaqueMVar hboxTy
  let atomProof ← hyps.foldrM (init := ← `(True.intro))
    (fun h acc => `(⟨by linarith [($h).1], by linarith [($h).2], $acc⟩))
  let rest ← Tactic.run hbox.mvarId! (do
    evalTactic (← `(tactic| intro t ht))
    evalTactic (← `(tactic| simp +decide only [Cycle63.Certificate.InBox,
      Cycle63.Certificate.tailPt, Function.update_apply, Cycle63.Certificate.RatExpr.ptOfList,
      List.getD_cons_zero, List.getD_cons_succ, ite_true, ite_false]))
    evalTactic (← `(tactic| all_goals push_cast at ht ⊢))
    evalTactic (← `(tactic| all_goals exact ⟨ht.1, ht.2, $atomProof⟩)))
  unless rest.isEmpty do throwError "rat_mono: the box condition left goals"
  let both := mkAppN (mkConst ``RatExpr.monotone_of_monoTest)
    #[kParams, increasingE, e, box, d, hcheck, x, loR, hiR, hbox]
  let rflE ← mkEqRefl increasingE
  let rest ← mkAppM ``And.right #[both]
  let side ← if increasing then mkAppM ``And.left #[both] else mkAppM ``And.left #[rest]
  let mono := mkApp side rflE
  let cont ← mkAppM ``And.right #[rest]
  let loSub ← match loHyp? with
    | some h => `((by linarith [($h).1]))
    | none => `((by norm_num))
  let hiSub ← match hiHyp? with
    | some h => `((by linarith [($h).2]))
    | none => `((by norm_num))
  -- Transfer a property of the expression on the segment to the goal's function and interval.
  let transfer (target proof : Expr) : TacticM Expr := do
    let final ← mkFreshExprSyntheticOpaqueMVar target
    let proofSyn ← Term.exprToSyntax proof
    let rest ← Tactic.run final.mvarId! (do
      evalTactic (← `(tactic| have hm := $proofSyn))
      evalTactic (← `(tactic| push_cast at hm))
      evalTactic (← `(tactic| refine (hm.mono ?_).congr ?_))
      evalTactic (← `(tactic| exact Set.Icc_subset_Icc $loSub $hiSub))
      evalTactic (← `(tactic| intro t _))
      evalTactic (← `(tactic| simp +decide only [Cycle63.Certificate.RatExpr.denote,
        Function.update_apply, Cycle63.Certificate.RatExpr.ptOfList, List.getD_cons_zero,
        List.getD_cons_succ, ite_true, ite_false]))
      evalTactic (← `(tactic| all_goals push_cast))
      evalTactic (← `(tactic| all_goals ring)))
    unless rest.isEmpty do throwError "rat_mono: the identity with the goal's function left goals"
    instantiateMVars final
  let monoProof ← transfer monoGoal mono
  match contGoal? with
  | none => goal.assign monoProof
  | some c => goal.assign (← mkAppM ``And.intro #[monoProof, ← transfer c cont])
  replaceMainGoal []

end Cycle63.Certificate
