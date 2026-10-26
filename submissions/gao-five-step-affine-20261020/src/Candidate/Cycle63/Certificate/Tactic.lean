/- The `rat_pos` tactic: proves `a < b` for rational expressions in variables confined to intervals,
by the kernel-evaluated Bernstein test of `Cycle63.Certificate.RatExpr`. Released under Apache 2.0. -/
import Candidate.Cycle63.Certificate.IntervalCoeffs
import Candidate.Cycle63.Certificate.RatExpr

set_option autoImplicit false

open Lean Meta Elab Tactic

namespace Cycle63.Certificate

/-- The rational number denoted by a numeral expression built from `OfNat`, `+`, `-`, `*`, `/`. -/
partial def ratOfExpr (e : Expr) : MetaM ℚ := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some k => return (k : ℚ)
    | none => throwError "rat_pos: {e} is not a numeral"
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => return (← ratOfExpr a) / (← ratOfExpr b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return (← ratOfExpr a) * (← ratOfExpr b)
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return (← ratOfExpr a) + (← ratOfExpr b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return (← ratOfExpr a) - (← ratOfExpr b)
  | (``Neg.neg, #[_, _, a]) => return -(← ratOfExpr a)
  | _ => throwError "rat_pos: {e} is not a rational numeral"

/-- A term of type `ℚ` for the rational number `q`. -/
def mkRatLit (q : ℚ) : MetaM Expr := do
  let ty := mkConst ``Rat
  let num ← mkNumeral ty q.num.natAbs
  let num ← if q.num < 0 then mkAppM ``Neg.neg #[num] else pure num
  if q.den = 1 then return num
  mkAppM ``HDiv.hDiv #[num, ← mkNumeral ty q.den]

/-- The `RatExpr` of a real expression whose leaves are numerals and the given atoms. Numeral
subexpressions such as `5/6` become single constants, so that they add nothing to denominators. -/
partial def reify (atoms : Array Expr) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if let some i := atoms.findIdx? (· == e) then
    return mkApp (mkConst ``RatExpr.var) (mkNatLit i)
  if let some q ← (try some <$> ratOfExpr e catch _ => pure none) then
    return mkApp (mkConst ``RatExpr.const) (← mkRatLit q)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``RatExpr.add) (← reify atoms a) (← reify atoms b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``RatExpr.sub) (← reify atoms a) (← reify atoms b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``RatExpr.mul) (← reify atoms a) (← reify atoms b)
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) =>
    return mkApp2 (mkConst ``RatExpr.div) (← reify atoms a) (← reify atoms b)
  | (``Neg.neg, #[_, _, a]) => return mkApp (mkConst ``RatExpr.neg) (← reify atoms a)
  | (``HPow.hPow, #[_, ty, _, _, a, n]) =>
    unless ← isDefEq ty (mkConst ``Nat) do
      throwError "rat_pos: exponent of {e} is not a natural number"
    return mkApp2 (mkConst ``RatExpr.pow) (← reify atoms a) n
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some k => return mkApp (mkConst ``RatExpr.const) (← mkRatLit k)
    | none => throwError "rat_pos: {e} is not a numeral"
  | _ => throwError "rat_pos: {e} is not a rational expression in the variables {atoms}"

/-- The variable and the two ends of a hypothesis `v ∈ Set.Icc lo hi` or `lo ≤ v ∧ v ≤ hi`. -/
def endsOfHyp (ty : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars ty
  match ty.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, s, v]) =>
    match s.getAppFnArgs with
    | (``Set.Icc, #[_, _, lo, hi]) => return (v, lo, hi)
    | _ => throwError "rat_pos: hypothesis {ty} is not of the form v ∈ Set.Icc lo hi"
  | (``And, #[l, r]) =>
    match l.getAppFnArgs, r.getAppFnArgs with
    | (``LE.le, #[_, _, lo, v]), (``LE.le, #[_, _, v', hi]) =>
      unless v == v' do throwError "rat_pos: the two bounds of {ty} are about different terms"
      return (v, lo, hi)
    | _, _ => throwError "rat_pos: hypothesis {ty} is not of the form lo ≤ v ∧ v ≤ hi"
  | _ => throwError "rat_pos: hypothesis {ty} is not of the form v ∈ Set.Icc lo hi"

/-- The rational outer bounds of the variables of the hypotheses `vᵢ ∈ [eᵢ, fᵢ]`: an end that is
not a numeral is another variable `vⱼ`, and is replaced by the same end of `vⱼ`'s interval. -/
def resolveEnds (entries : Array (Expr × Expr × Expr)) : MetaM (Array (ℚ × ℚ)) := do
  let numeral? (e : Expr) : MetaM (Option ℚ) := try some <$> ratOfExpr e catch _ => pure none
  let resolve (e : Expr) (lower : Bool) : MetaM ℚ := do
    let mut cur := e
    for _ in [0:entries.size + 1] do
      if let some q ← numeral? cur then return q
      -- Up to definitional equality: instance arguments may differ in their proof terms.
      let mut next : Option Expr := none
      for (v, lo, hi) in entries do
        if next.isNone then
          if ← isDefEq v cur then next := some (if lower then lo else hi)
      match next with
      | some e => cur := e
      | none => throwError "rat_pos: the interval end {cur} is neither a numeral nor a variable"
    throwError "rat_pos: the interval ends of the variables form a cycle"
  entries.mapM fun (_, lo, hi) => return (← resolve lo true, ← resolve hi false)

/-- The variable and the interval of a hypothesis `v ∈ Set.Icc lo hi` or `lo ≤ v ∧ v ≤ hi`. -/
def boxOfHyp (ty : Expr) : MetaM (Expr × ℚ × ℚ) := do
  let ty ← instantiateMVars ty
  match ty.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, s, v]) =>
    match s.getAppFnArgs with
    | (``Set.Icc, #[_, _, lo, hi]) => return (v, ← ratOfExpr lo, ← ratOfExpr hi)
    | _ => throwError "rat_pos: hypothesis {ty} is not of the form v ∈ Set.Icc lo hi"
  | (``And, #[l, r]) =>
    match l.getAppFnArgs, r.getAppFnArgs with
    | (``LE.le, #[_, _, lo, v]), (``LE.le, #[_, _, v', hi]) =>
      unless v == v' do throwError "rat_pos: the two bounds of {ty} are about different terms"
      return (v, ← ratOfExpr lo, ← ratOfExpr hi)
    | _, _ => throwError "rat_pos: hypothesis {ty} is not of the form lo ≤ v ∧ v ≤ hi"
  | _ => throwError "rat_pos: hypothesis {ty} is not of the form v ∈ Set.Icc lo hi"

/-- The two sides of a hypothesis `a ≤ b` or `a < b`, and a proof of `a ≤ b`. -/
def sidesOfConstraint (h : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty := (← instantiateMVars (← inferType h)).consumeMData
  match ty.getAppFnArgs with
  | (``LE.le, #[_, _, a, b]) => return (a, b, h)
  | (``LT.lt, #[_, _, a, b]) => return (a, b, ← mkAppM ``le_of_lt #[h])
  | _ => throwError "rat_pos: constraint {ty} is not of the form a ≤ b or a < b"

/-- A proof of `RatExpr.denote e pt = rhs`, by unfolding the denotation and `ring`. -/
def denoteIdentity (e pt rhs : Expr) : TacticM Expr := do
  let ty ← mkEq (← mkAppM ``RatExpr.denote #[e, pt]) rhs
  let proof ← mkFreshExprSyntheticOpaqueMVar ty
  let rest ← Tactic.run proof.mvarId! (do
    evalTactic (← `(tactic| simp only [Cycle63.Certificate.RatExpr.denote,
      Cycle63.Certificate.RatExpr.ptOfList, List.getD_cons_zero, List.getD_cons_succ]))
    evalTactic (← `(tactic| all_goals push_cast))
    evalTactic (← `(tactic| all_goals first | with_reducible rfl | ring)))
  unless rest.isEmpty do throwError "rat_pos: the expression identity left goals"
  return proof

/-- Options of `rat_pos`: the bisection depth of each polynomial test and of the box. -/
declare_syntax_cat ratPosOption
syntax " (" &"depth" " := " num ")" : ratPosOption
syntax " (" &"split" " := " num ")" : ratPosOption

/-- `rat_pos (depth := d) (split := n) [h₁, …, hₖ] given [c₁, …, cₘ]` proves a goal `a < b` in
which `a` and `b` are rational expressions in variables `vᵢ` with hypotheses
`hᵢ : vᵢ ∈ Set.Icc loᵢ hiᵢ` or `hᵢ : loᵢ ≤ vᵢ ∧ vᵢ ≤ hiᵢ`, where each end is a rational numeral or
another variable `vⱼ`, whose interval then supplies the bound. The numerator and denominator of `b - a` are computed
in Lean and their positivity on the box is checked by the kernel with product-form Bernstein
coefficients, bisecting each polynomial's box up to depth `d` (default 6). The optional constraints
`cⱼ : aⱼ ≤ bⱼ` (or `<`), rational expressions in the same variables, restrict the claim to the part of
the box where they hold: the box is bisected up to depth `n` (default 8), and each sub-box either
shows `b - a > 0` or shows some `bⱼ - aⱼ < 0`. -/
syntax (name := ratPosTac) "rat_pos" (ratPosOption)* " [" term,* "]" (&"given" " [" term,* "]")? :
  tactic

unsafe def evalBoolUnsafe (e : Expr) : MetaM Bool := evalExpr Bool (mkConst ``Bool) e

/-- The value of a closed Boolean term, by compiled code. -/
@[implemented_by evalBoolUnsafe]
opaque evalBool (e : Expr) : MetaM Bool

/-- The first `min` or `max` of two real numbers in an expression. -/
def findMinMax? (e : Expr) : Option Expr :=
  e.find? fun s =>
    (s.isAppOfArity ``Min.min 4 || s.isAppOfArity ``Max.max 4) && s.getAppArgs[0]!.isConstOf ``Real

@[tactic ratPosTac] def evalRatPos : Tactic := fun stx => withMainContext do
  -- A `min` or `max` in the goal or in a constraint: prove the two cases, each with the active
  -- branch substituted and the case condition as a further constraint.
  let options : Array (TSyntax `ratPosOption) := stx[1].getArgs.map (⟨·⟩)
  let boxHyps : Array (TSyntax `term) := stx[3].getSepArgs.map (⟨·⟩)
  let givenHyps : Array (TSyntax `term) :=
    if stx[5].getNumArgs = 0 then #[] else stx[5][2].getSepArgs.map (⟨·⟩)
  let goalType := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let mut types : Array Expr := #[goalType]
  for c in givenHyps do
    types := types.push (← instantiateMVars (← inferType (← elabTerm c none))).consumeMData
  if let some m := types.findSome? findMinMax? then
    let a ← Term.exprToSyntax m.getAppArgs[2]!
    let b ← Term.exprToSyntax m.getAppArgs[3]!
    let (whenLe, whenGe) : Name × Name :=
      if m.isAppOf ``Min.min then (``min_eq_left, ``min_eq_right) else (``max_eq_right, ``max_eq_left)
    let leIdent := mkIdent whenLe
    let geIdent := mkIdent whenGe
    -- A plain name, numbered by the constraint count, so that nested splits stay distinct.
    let hsplit := mkIdent (Name.mkSimple s!"rat_pos_split_{givenHyps.size}")
    let given := givenHyps.push ⟨hsplit.raw⟩
    evalTactic (← `(tactic| (
      obtain $hsplit:ident | $hsplit:ident := le_total $a $b
      · (try rw [$leIdent:ident $hsplit:ident] at *)
        rat_pos $options* [$boxHyps,*] given [$given,*]
      · (try rw [$geIdent:ident $hsplit:ident] at *)
        rat_pos $options* [$boxHyps,*] given [$given,*])))
    return
  let mut depth : ℕ := 6
  let mut split : ℕ := 8
  for option in stx[1].getArgs do
    let value ← match option[3].isNatLit? with
      | some v => pure v
      | none => throwError "rat_pos: option {option} has no numeral value"
    match option[1].getAtomVal with
    | "depth" => depth := value
    | "split" => split := value
    | name => throwError "rat_pos: unknown option {name}"
  let hyps : Array (TSyntax `term) := stx[3].getSepArgs.map (⟨·⟩)
  let constraints : Array (TSyntax `term) :=
    if stx[5].getNumArgs = 0 then #[] else stx[5][2].getSepArgs.map (⟨·⟩)
  let mut entries : Array (Expr × Expr × Expr) := #[]
  for h in hyps do
    entries := entries.push (← endsOfHyp (← inferType (← elabTerm h none)))
  let atoms := entries.map (·.1)
  let mut boxElems : Array Expr := #[]
  let ends ← resolveEnds entries
  for (lo, hi) in ends do
    boxElems := boxElems.push (← mkAppM ``Prod.mk #[← mkRatLit lo, ← mkRatLit hi])
  -- The trailing variables confined to intervals of width at most `10⁻⁶` are reduced to the
  -- midpoints of interval enclosures instead of being expanded in the Bernstein basis.
  let thin := (ends.toList.reverse.takeWhile fun (lo, hi) => hi - lo ≤ 1/1000000).length
  let goal ← getMainGoal
  let gty := (← instantiateMVars (← goal.getType)).consumeMData
  let (a, b) ← match gty.getAppFnArgs with
    | (``LT.lt, #[_, _, a, b]) => pure (a, b)
    | _ => throwError "rat_pos: the goal {gty} is not a strict inequality"
  let e := mkApp2 (mkConst ``RatExpr.sub) (← reify atoms b) (← reify atoms a)
  let ratPairTy ← mkAppM ``Prod #[mkConst ``Rat, mkConst ``Rat]
  let box ← mkListLit ratPairTy boxElems.toList
  let pt := mkApp (mkConst ``RatExpr.ptOfList) (← mkListLit (mkConst ``Real) atoms.toList)
  let k := mkNatLit atoms.size
  let d := mkNatLit depth
  -- The constraints as expressions `bⱼ - aⱼ`, with proofs that they are nonnegative at the point.
  let mut conds : Array Expr := #[]
  let mut condProofs : Array Expr := #[]
  for c in constraints do
    let hc ← elabTerm c none
    let (ca, cb, hle) ← sidesOfConstraint hc
    let ce := mkApp2 (mkConst ``RatExpr.sub) (← reify atoms cb) (← reify atoms ca)
    let heq ← denoteIdentity ce pt (← mkAppM ``HSub.hSub #[cb, ca])
    let hnn ← mkAppM ``sub_nonneg_of_le #[hle]
    conds := conds.push ce
    condProofs := condProofs.push (← mkAppM ``LE.le.trans_eq #[hnn, ← mkEqSymm heq])
  let condList ← mkListLit (mkConst ``RatExpr) conds.toList
  let checkWith (C : Expr) : MetaM Expr := if constraints.isEmpty then
      mkAppM ``RatExpr.ratPos #[C, e, box, d]
    else
      mkAppM ``RatExpr.ratPosOn #[C, condList, e, box, d, mkNatLit split]
  let mixed := mkApp2 (mkConst ``reducedCoeffs) (mkNatLit thin) (mkNatLit (atoms.size - thin))
  let C ← if thin > 0 && (← evalBool (← checkWith mixed)) then pure mixed
    else pure (mkApp (mkConst ``coeffsN) k)
  let check ← checkWith C
  let hcheck ← mkFreshExprSyntheticOpaqueMVar (← mkEq check (mkConst ``Bool.true))
  let rest ← Tactic.run hcheck.mvarId! (evalTactic (← `(tactic| decide +kernel)))
  unless rest.isEmpty do throwError "rat_pos: the kernel check left goals"
  let hboxTy ← mkAppM ``InBox #[box, pt]
  let hbox ← mkFreshExprSyntheticOpaqueMVar hboxTy
  -- Each bound follows from the hypotheses by `linarith`, through the intervals of the variables
  -- that are interval ends.
  let parts : Array (TSyntax `term) ← hyps.foldlM (init := #[])
    (fun acc h => return acc.push (← `(($h).1)) |>.push (← `(($h).2)))
  let boxProof ← hyps.foldrM (init := ← `(True.intro))
    (fun _ acc => `(⟨by linarith [$parts,*], by linarith [$parts,*], $acc⟩))
  let rest ← Tactic.run hbox.mvarId! (do
    evalTactic (← `(tactic| simp only [Cycle63.Certificate.InBox, Cycle63.Certificate.tailPt,
      Cycle63.Certificate.RatExpr.ptOfList, List.getD_cons_zero, List.getD_cons_succ]))
    evalTactic (← `(tactic| all_goals push_cast))
    evalTactic (← `(tactic| all_goals exact $boxProof)))
  unless rest.isEmpty do throwError "rat_pos: the box hypotheses left goals"
  let he ← denoteIdentity e pt (← mkAppM ``HSub.hSub #[b, a])
  let proof ← if constraints.isEmpty then
      mkAppM ``RatExpr.lt_of_ratPos #[C, e, box, d, hcheck, pt, hbox, he]
    else do
      let hconds ← condProofs.foldrM (init := mkConst ``True.intro)
        (fun p acc => mkAppM ``And.intro #[p, acc])
      mkAppM ``RatExpr.lt_of_ratPosOn
        #[C, condList, e, box, d, mkNatLit split, hcheck, pt, hbox, hconds, he]
  goal.assign proof
  replaceMainGoal []

end Cycle63.Certificate
