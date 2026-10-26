import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Reconstruct
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Derivative
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Tactic
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The `rat_mono` tactic: proves `StrictMonoOn f (Set.Icc a b)` or `StrictAntiOn f (Set.Icc a b)`,
alone or together with `ContinuousOn f (Set.Icc a b)`, for a rational expression `f` in one variable
and parameters confined to intervals. The expression is first brought to lowest terms `P/Q` at
elaboration time; the kernel checks that `P/Q` agrees with it (`Reduction`), the sign tests of
`RatExpr.monoSides` on `P/Q`, whose degrees are small, and the positivity of `P' Q - P Q'`, which is
computed at elaboration time and checked once, on the pieces of a bisection of the box, each in its
own kernel check. Released under Apache 2.0. -/
set_option autoImplicit false

open Lean Meta Elab Tactic

namespace Cycle63.Certificate

namespace RatExpr

theorem agreeOnGrid_append_of (e₁ e₂ : RatExpr) (s t : List ℤ) (rest : List (List ℤ))
    (hs : agreeOnGrid e₁ e₂ (s :: rest) = true) (ht : agreeOnGrid e₁ e₂ (t :: rest) = true) :
    agreeOnGrid e₁ e₂ ((s ++ t) :: rest) = true := by
  rw [agreeOnGrid_append, hs, ht, Bool.and_self]

/-- Strict monotonicity and continuity of an expression along its first coordinate on `[a, b]`
from those of the quotient `P/Q` of polynomials that agrees with it: the cross products agree on an
admissible grid, `Q` and the certified divisors of the expression do not vanish on the box. -/
theorem monotone_of_reduction (k : ℕ) (S : Coeffs (PolyN (k + 1)))
    (hS : ∀ r x, S.eval r x = (coeffsN (k + 1)).eval r x) (increasing : Bool) (e P Q : RatExpr)
    (box : List (ℚ × ℚ)) (d : ℕ) (grid : List (List ℤ))
    (certs : List (RatExpr × RatExpr × RatExpr))
    (hsides : monoSides k S (div P Q) box d = true) (p : PolyN (k + 1))
    (hbeq : (coeffsN (k + 1)).beq p (derivPoly k increasing (div P Q)) = true)
    (hpos : posOnSplit S p box d = true)
    (hadm : gridAdmissible e (div P Q) grid = true) (hagree : agreeOnGrid e (div P Q) grid = true)
    (hcert : divisorsCertified k S d box e certs = true) (hP : (divisors P).isEmpty = true)
    (hQ : polySign k S d box Q = true)
    (x : ℕ → ℝ) (a b : ℝ) (hbox : ∀ t ∈ Set.Icc a b, InBox box (Function.update x 0 t)) :
    (increasing = true → StrictMonoOn (fun t => e.denote (Function.update x 0 t)) (Set.Icc a b)) ∧
      (increasing = false →
        StrictAntiOn (fun t => e.denote (Function.update x 0 t)) (Set.Icc a b)) ∧
      ContinuousOn (fun t => e.denote (Function.update x 0 t)) (Set.Icc a b) := by
  obtain ⟨hinc, hdec, hcont⟩ :=
    monotone_of_parts k S hS increasing (div P Q) box d hsides p hbeq hpos x a b hbox
  simp only [List.isEmpty_iff] at hP
  have heq : Set.EqOn (fun t => (div P Q).denote (Function.update x 0 t))
      (fun t => e.denote (Function.update x 0 t)) (Set.Icc a b) := fun t ht => by
    obtain ⟨hQnil, hQ0⟩ := ne_zero_of_polySign k S hS d box Q hQ _ (hbox t ht)
    have hPQ : DivisorsNonzero (Function.update x 0 t) (div P Q) :=
      ⟨divisorsNonzero_of_forall _ P (by simp [hP]), divisorsNonzero_of_forall _ Q (by simp [hQnil]),
        hQ0⟩
    exact (denote_eq_of_agreeOnGrid e (div P Q) grid hadm hagree _
      (divisorsNonzero_of_certified k S hS d box e certs hcert _ (hbox t ht)) hPQ).symm
  exact ⟨fun h => (hinc h).congr heq, fun h => (hdec h).congr heq, hcont.congr fun t ht => (heq ht).symm⟩

end RatExpr

/-- A polynomial in several variables as a tree of coefficient lists, to read the value of a
`PolyN` term at elaboration time. -/
inductive PolyTree where
  | leaf (c : ℚ)
  | node (cs : List PolyTree)

/-- The tree of a polynomial in `k` variables. -/
def polyTree : (k : ℕ) → PolyN k → PolyTree
  | 0, c => .leaf c
  | k + 1, cs => .node ((cs : List (PolyN k)).map (polyTree k))

unsafe def evalPolyTreeUnsafe (e : Expr) : MetaM PolyTree := evalExpr PolyTree (mkConst ``PolyTree) e

/-- The value of a closed `PolyTree` term. -/
@[implemented_by evalPolyTreeUnsafe]
opaque evalPolyTree (e : Expr) : MetaM PolyTree

/-- The `PolyN k` term of a polynomial in `k` variables from its tree. -/
def polyNExpr : ℕ → PolyTree → MetaM Expr
  | 0, .leaf c => mkRatLit c
  | k + 1, .node cs => do
    mkListLit (mkApp (mkConst ``PolyN) (mkNatLit k)) (← cs.mapM (polyNExpr k))
  | _, _ => throwError "polyNExpr: the tree does not have the depth of its type"

/-- A proof of `lhs = true` by the kernel. -/
def kernelDecide (lhs : Expr) : TacticM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs (mkConst ``Bool.true))
  let restGoals ← Tactic.run m.mvarId! (evalTactic (← `(tactic| decide +kernel)))
  unless restGoals.isEmpty do throwError "rat_mono: a kernel check left goals"
  instantiateMVars m

/-- A proof of `posOnSplit S p box d = true` for polynomials of type `R`: where the direct test fails
at elaboration time, the box is bisected, up to `levels` times, and the kernel checks each piece
separately, so that no single check holds the whole bisection. -/
partial def posOnSplitProof (R S p box : Expr) (d levels : ℕ) : TacticM Expr := do
  if levels == 0 || d == 0 || (← evalBool (mkAppN (mkConst ``Coeffs.posOn) #[R, S, p, box])) then
    kernelDecide (mkAppN (mkConst ``posOnSplit) #[R, S, p, box, mkNatLit d])
  else
    let halves := mkApp2 (mkConst ``splitBox) box (mkApp (mkConst ``widestIndex) box)
    let h₁ ← posOnSplitProof R S p (← mkAppM ``Prod.fst #[halves]) (d - 1) (levels - 1)
    let h₂ ← posOnSplitProof R S p (← mkAppM ``Prod.snd #[halves]) (d - 1) (levels - 1)
    return mkAppN (mkConst ``posOnSplit_of_halves) #[R, S, p, box, mkNatLit (d - 1), h₁, h₂]

/-- The `RatExpr` term of a polynomial in Horner form in the variables from `i` on: a polynomial in
`xᵢ` whose coefficients are polynomials in the later variables, so that the kernel multiplies out no
powers of a variable when it computes the fraction of the term. -/
partial def polyExpr (F : Reconstruct.Poly) (i nvars : ℕ) : MetaM Expr := do
  if i ≥ nvars then
    return mkApp (mkConst ``RatExpr.const) (← mkRatLit (F.foldl (fun s t => s + t.2) 0))
  let power (n : ℕ) : Expr :=
    let x := mkApp (mkConst ``RatExpr.var) (mkNatLit i)
    if n == 1 then x else mkApp2 (mkConst ``RatExpr.pow) x (mkNatLit n)
  let coefficient (j : ℕ) : MetaM Expr := polyExpr (F.filter fun t => t.1.getD i 0 == j) (i + 1) nvars
  match ((F.map fun t => t.1.getD i 0).qsort (· < ·)).toList.eraseDups.reverse with
  | [] => return mkApp (mkConst ``RatExpr.const) (← mkRatLit 0)
  | top :: lower =>
    let mut acc ← coefficient top
    let mut above := top
    for j in lower do
      acc := mkApp2 (mkConst ``RatExpr.add) (← coefficient j)
        (mkApp2 (mkConst ``RatExpr.mul) (power (above - j)) acc)
      above := j
    if above > 0 then
      acc := mkApp2 (mkConst ``RatExpr.mul) (power above) acc
    return acc

/-- The divisors of a reified `RatExpr` term, innermost first, without repetitions. -/
partial def divisorExprs (e : Expr) : List Expr :=
  (go e []).reverse
where
  go (e : Expr) (acc : List Expr) : List Expr :=
    match e.getAppFnArgs with
    | (``RatExpr.add, #[a, b]) | (``RatExpr.sub, #[a, b]) | (``RatExpr.mul, #[a, b]) => go b (go a acc)
    | (``RatExpr.div, #[a, b]) =>
      let acc := go b (go a acc)
      if acc.contains b then acc else b :: acc
    | (``RatExpr.neg, #[a]) | (``RatExpr.pow, #[a, _]) => go a acc
    | _ => acc

unsafe def evalRatExprUnsafe (e : Expr) : MetaM RatExpr := evalExpr RatExpr (mkConst ``RatExpr) e

/-- The value of a closed `RatExpr` term. -/
@[implemented_by evalRatExprUnsafe]
opaque evalRatExpr (e : Expr) : MetaM RatExpr

/-- A list of natural numbers as a term of type `List ℤ`. -/
def intListExpr (ns : List ℕ) : MetaM Expr := do
  mkListLit (mkConst ``Int) (← ns.mapM fun k => mkAppM ``Int.ofNat #[mkNatLit k])

/-- The terms of the pairs of a box. -/
def boxExpr (box : List (ℚ × ℚ)) : MetaM Expr := do
  let ty ← mkAppM ``Prod #[mkConst ``Rat, mkConst ``Rat]
  mkListLit ty (← box.mapM fun (lo, hi) => do mkAppM ``Prod.mk #[← mkRatLit lo, ← mkRatLit hi])

/-- `rat_mono (depth := d) [h₁, …, hₖ]` proves a goal `StrictMonoOn (fun t => f t) (Set.Icc a b)`
or `StrictAntiOn (fun t => f t) (Set.Icc a b)`, or either of them in a conjunction with
`ContinuousOn (fun t => f t) (Set.Icc a b)`, with rational `a`, `b`, for a rational expression
`f t` in `t` and parameters `vᵢ` with hypotheses `hᵢ : vᵢ ∈ Set.Icc loᵢ hiᵢ` or
`hᵢ : loᵢ ≤ vᵢ ∧ vᵢ ≤ hiᵢ`. An end of the interval may also be one of the `vᵢ`: the segment is then
extended to the outer bound of that parameter, and the result restricted to the interval. At
elaboration time `f` and each of its divisors are brought to lowest terms, quotients of polynomials
`P/Q`. The kernel checks that each quotient agrees with its expression on a grid of integer points
larger than the degree bounds, that the polynomials of the divisors and the denominator `Q` have
strict signs on the box `[a, b] × ∏ [loᵢ, hiᵢ]`, and that `P' Q - P Q'` (or its negative) is positive
there, with bisection up to depth `d` (default 6); the mean value theorem gives the monotonicity.
The polynomials are written in Horner form, and the pieces of the bisection are checked separately. -/
syntax (name := ratMonoTac) "rat_mono" (ratPosOption)* " [" term,* "]" : tactic

@[tactic ratMonoTac] def evalRatMono : Tactic := fun stx => withMainContext do
  let mut depth : ℕ := 6
  let chunk : ℕ := 12
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
  let (monoGoal, contGoal?) := match gty.getAppFnArgs with
    | (``And, #[m, c]) => (m.consumeMData, some c.consumeMData)
    | _ => (gty, none)
  let (increasing, f, s) ← match monoGoal.getAppFnArgs with
    | (``StrictMonoOn, #[_, _, _, _, f, s]) => pure (true, f, s)
    | (``StrictAntiOn, #[_, _, _, _, f, s]) => pure (false, f, s)
    | _ => throwError "rat_mono: the goal {gty} is not StrictMonoOn or StrictAntiOn"
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
  let endOf (e : Expr) (outer : (ℚ × ℚ) → ℚ) : MetaM (ℚ × Option (TSyntax `term)) := do
    if let some q ← (try some <$> ratOfExpr e catch _ => pure none) then return (q, none)
    for i in [0:atoms.size] do
      if ← isDefEq atoms[i]! e then return (outer bounds[i]!, some atomHyps[i]!)
    throwError "rat_mono: the interval end {e} is neither a numeral nor a parameter"
  let (lo, loHyp?) ← endOf loE (·.1)
  let (hi, hiHyp?) ← endOf hiE (·.2)
  let boxList : List (ℚ × ℚ) := (lo, hi) :: bounds.toList
  let box ← boxExpr boxList
  let rest ← boxExpr bounds.toList
  let e ← withLocalDeclD `t (mkConst ``Real) fun t => reify (#[t] ++ atoms) (mkApp f t).headBeta
  let ev ← evalRatExpr e
  let nvars := atoms.size + 1
  -- The reduced fraction, by exact linear algebra at elaboration time.
  let some (P, Q) := Reconstruct.reduce ev nvars 60
    | throwError "rat_mono: no fraction of total degree at most 60 agrees with the expression"
  let PE ← polyExpr P 0 nvars
  let QE ← polyExpr Q 0 nvars
  let pv ← evalRatExpr PE
  let qv ← evalRatExpr QE
  let e₂v := RatExpr.div pv qv
  let e₂ := mkApp2 (mkConst ``RatExpr.div) PE QE
  -- The grid: per variable, one more distinct point than the degree bound of the cross difference.
  let gridLists : List (List ℕ) := (List.range nvars).map fun i =>
    List.range (RatExpr.crossDeg ev e₂v i + 1)
  let firstChunks : List (List ℕ) := (gridLists.headD []).toChunks chunk
  let restGrid ← mkListLit (← mkAppM ``List #[mkConst ``Int])
    (← (gridLists.tail.mapM intListExpr : MetaM (List Expr)))
  let chunkExprs ← (firstChunks.mapM intListExpr : MetaM (List Expr))
  let firstE ← match chunkExprs.reverse with
    | [] => intListExpr []
    | last :: earlier => earlier.foldlM (fun acc c => mkAppM ``HAppend.hAppend #[c, acc]) last
  let gridE ← mkAppM ``List.cons #[firstE, restGrid]
  -- Certificates of the divisors, innermost first: each one as a quotient of polynomials.
  let mut certExprs : Array Expr := #[]
  for b in divisorExprs e do
    let bv ← evalRatExpr b
    let (Pb, Qb) ← if (RatExpr.divisors bv).isEmpty then
        pure (b, mkApp (mkConst ``RatExpr.const) (← mkRatLit 1))
      else match Reconstruct.reduce bv nvars 60 with
        | some (P', Q') => pure (← polyExpr P' 0 nvars, ← polyExpr Q' 0 nvars)
        | none => throwError "rat_mono: no fraction of total degree at most 60 agrees with the divisor {b}"
    certExprs := certExprs.push (← mkAppM ``Prod.mk #[b, ← mkAppM ``Prod.mk #[Pb, Qb]])
  let tripleTy ← mkAppM ``Prod #[mkConst ``RatExpr, ← mkAppM ``Prod #[mkConst ``RatExpr, mkConst ``RatExpr]]
  let certsE ← mkListLit tripleTy certExprs.toList
  let increasingE := if increasing then mkConst ``Bool.true else mkConst ``Bool.false
  let kE := mkNatLit atoms.size
  let dE := mkNatLit depth
  -- The sign tests reduce the trailing parameters confined to intervals of width at most `10⁻⁶`
  -- to the midpoints of their interval enclosures, when that test succeeds.
  let thin := (boxList.reverse.takeWhile fun (lo, hi) => hi - lo ≤ 1/1000000).length
  let reduced := mkApp2 (mkConst ``reducedCoeffs) (mkNatLit thin) (mkNatLit (nvars - thin))
  let S ← if thin > 0 && (← evalBool
        (mkAppN (mkConst ``RatExpr.monoTest) #[kE, reduced, increasingE, e₂, box, dE])) then
      pure reduced
    else pure (mkApp (mkConst ``coeffsN) (mkNatLit nvars))
  let Ssyn ← Term.exprToSyntax S
  let nvarsSyn := Syntax.mkNumLit (toString nvars)
  let hS ← instantiateMVars (← Tactic.elabTerm (← `((fun _ _ => rfl :
      ∀ r x, Cycle63.Certificate.Coeffs.eval $Ssyn r x =
        Cycle63.Certificate.Coeffs.eval (Cycle63.Certificate.coeffsN $nvarsSyn) r x))) none)
  let decideTrue := kernelDecide
  let hsides ← decideTrue (mkAppN (mkConst ``RatExpr.monoSides) #[kE, S, e₂, box, dE])
  -- The derivative polynomial is computed once, at elaboration time, and checked by the kernel
  -- once; its positivity is checked on the pieces of the box.
  let R := mkApp (mkConst ``PolyN) (mkNatLit nvars)
  let derivE := mkAppN (mkConst ``RatExpr.derivPoly) #[kE, increasingE, e₂]
  let pLit ← polyNExpr nvars (← evalPolyTree (mkApp2 (mkConst ``polyTree) (mkNatLit nvars) derivE))
  let hbeq ← decideTrue
    (mkAppN (mkConst ``Coeffs.beq) #[R, mkApp (mkConst ``coeffsN) (mkNatLit nvars), pLit, derivE])
  let hpos ← posOnSplitProof R S pLit box depth 4
  let hadm ← decideTrue (mkAppN (mkConst ``RatExpr.gridAdmissible) #[e, e₂, gridE])
  -- The identity, one chunk of the first coordinate at a time.
  let mut chunkProofs : Array (Expr × Expr) := #[]
  for c in chunkExprs do
    let proof ← decideTrue (mkAppN (mkConst ``RatExpr.agreeOnGrid) #[e, e₂, ← mkAppM ``List.cons #[c, restGrid]])
    chunkProofs := chunkProofs.push (c, proof)
  let hagree ← match chunkProofs.toList.reverse with
    | [] => throwError "rat_mono: empty grid"
    | (cLast, pLast) :: earlier =>
      Prod.snd <$> earlier.foldlM (fun (accList, accProof) (c, proof) => do
        let combined := mkAppN (mkConst ``RatExpr.agreeOnGrid_append_of)
          #[e, e₂, c, accList, restGrid, proof, accProof]
        return (← mkAppM ``HAppend.hAppend #[c, accList], combined)) (cLast, pLast)
  let hcert ← decideTrue (mkAppN (mkConst ``RatExpr.divisorsCertified) #[kE, S, dE, box, e, certsE])
  let hP ← decideTrue (← mkAppM ``List.isEmpty #[mkApp (mkConst ``RatExpr.divisors) PE])
  let hQ ← decideTrue (mkAppN (mkConst ``RatExpr.polySign) #[kE, S, dE, box, QE])
  let zero ← mkAppOptM ``OfNat.ofNat #[mkConst ``Real, mkRawNatLit 0, none]
  let x := mkApp (mkConst ``RatExpr.ptOfList) (← mkListLit (mkConst ``Real) (zero :: atoms.toList))
  let loR ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, ← mkRatLit lo]
  let hiR ← mkAppOptM ``Rat.cast #[mkConst ``Real, none, ← mkRatLit hi]
  let segment ← mkAppM ``Set.Icc #[loR, hiR]
  let hboxTy ← withLocalDeclD `t (mkConst ``Real) fun t => do
    let mem ← mkAppM ``Membership.mem #[segment, t]
    let inBox ← mkAppM ``InBox #[box, ← mkAppM ``Function.update #[x, mkNatLit 0, t]]
    mkForallFVars #[t] (← mkArrow mem inBox)
  let hbox ← mkFreshExprSyntheticOpaqueMVar hboxTy
  let atomProof ← hyps.foldrM (init := ← `(True.intro))
    (fun h acc => `(⟨by linarith [($h).1], by linarith [($h).2], $acc⟩))
  let restGoals ← Tactic.run hbox.mvarId! (do
    evalTactic (← `(tactic| intro t ht))
    evalTactic (← `(tactic| simp +decide only [Cycle63.Certificate.InBox,
      Cycle63.Certificate.tailPt, Function.update_apply, Cycle63.Certificate.RatExpr.ptOfList,
      List.getD_cons_zero, List.getD_cons_succ, ite_true, ite_false]))
    evalTactic (← `(tactic| all_goals push_cast at ht ⊢))
    evalTactic (← `(tactic| all_goals exact ⟨ht.1, ht.2, $atomProof⟩)))
  unless restGoals.isEmpty do throwError "rat_mono: the box condition left goals"
  let both := mkAppN (mkConst ``RatExpr.monotone_of_reduction)
    #[kE, S, hS, increasingE, e, PE, QE, box, dE, gridE, certsE, hsides, pLit, hbeq, hpos, hadm,
      hagree, hcert, hP, hQ, x, loR, hiR, hbox]
  let rflE ← mkEqRefl increasingE
  let restAnd ← mkAppM ``And.right #[both]
  let side ← if increasing then mkAppM ``And.left #[both] else mkAppM ``And.left #[restAnd]
  let mono := mkApp side rflE
  let cont ← mkAppM ``And.right #[restAnd]
  let loSub ← match loHyp? with
    | some h => `((by linarith [($h).1]))
    | none => `((by norm_num))
  let hiSub ← match hiHyp? with
    | some h => `((by linarith [($h).2]))
    | none => `((by norm_num))
  let transfer (target proof : Expr) : TacticM Expr := do
    let final ← mkFreshExprSyntheticOpaqueMVar target
    let proofSyn ← Term.exprToSyntax proof
    let restGoals ← Tactic.run final.mvarId! (do
      evalTactic (← `(tactic| have hm := $proofSyn))
      evalTactic (← `(tactic| push_cast at hm))
      evalTactic (← `(tactic| refine (hm.mono ?_).congr ?_))
      evalTactic (← `(tactic| exact Set.Icc_subset_Icc $loSub $hiSub))
      evalTactic (← `(tactic| intro t _))
      evalTactic (← `(tactic| simp +decide only [Cycle63.Certificate.RatExpr.denote,
        Function.update_apply, Cycle63.Certificate.RatExpr.ptOfList, List.getD_cons_zero,
        List.getD_cons_succ, ite_true, ite_false]))
      evalTactic (← `(tactic| all_goals push_cast))
      evalTactic (← `(tactic| all_goals first | with_reducible rfl | ring)))
    unless restGoals.isEmpty do throwError "rat_mono: the identity with the goal's function left goals"
    instantiateMVars final
  let monoProof ← transfer monoGoal mono
  match contGoal? with
  | none => goal.assign monoProof
  | some c => goal.assign (← mkAppM ``And.intro #[monoProof, ← transfer c cont])
  replaceMainGoal []

end Cycle63.Certificate

end Record1252270103Bootstrap.PR67
