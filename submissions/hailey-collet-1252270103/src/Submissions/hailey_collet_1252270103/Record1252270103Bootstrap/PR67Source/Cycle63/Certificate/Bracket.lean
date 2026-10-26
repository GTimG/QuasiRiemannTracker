import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Interval
import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Tactic
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The `bracket` command: states and proves rational bounds `lo ≤ e ∧ e ≤ hi` of a real expression
`e` whose atoms have known bounds. The bounds are computed at elaboration time by the interval
evaluation of `Cycle63.Certificate.Interval` and checked by the kernel, so they never appear in the
source. Released under Apache 2.0. -/
set_option autoImplicit false

open Lean Meta Elab Command Term

namespace Cycle63.Certificate

/-- The constants to unfold in a reification: the listed ones, or every definition (`all`); the
reifier records the constants it unfolds in `used`. -/
structure Unfolding where
  names : Array Name
  all : Bool
  used : IO.Ref NameSet

/-- The `CExpr` of a real expression built from numerals, the given atoms, the field operations,
natural powers, `Real.sqrt`, `min` and `max`; head constants that `unfold` allows are unfolded. -/
partial def reifyBracket (atoms : Array Expr) (unfold : Unfolding) (e : Expr) : MetaM Expr := do
  let e := (← instantiateMVars e).headBeta
  if let some i := atoms.findIdx? (· == e) then
    return mkApp (mkConst ``CExpr.var) (mkNatLit i)
  -- A field of a structure value: unfold the value and reduce the projection, without unfolding
  -- the field itself.
  if let .proj _ _ s := e then
    let s' ← match ← unfoldDefinition? s with
      | some s' =>
        if let some n := s.getAppFn.constName? then unfold.used.modify (·.insert n)
        pure s'
      | none => pure s
    let r ← whnfCore (e.updateProj! s')
    if r == e then throwError "bracket: cannot reduce the projection {e}"
    return ← reifyBracket atoms unfold r
  if let .const c _ := e.getAppFn then
    -- A field accessor (not a type-class projection) applied to a structure value whose name is in
    -- the unfolding list.
    if let some info ← getProjectionFnInfo? c then
      let args := e.getAppArgs
      if !info.fromClass && info.numParams < args.size then
        if let some s := args[info.numParams]!.getAppFn.constName? then
          if unfold.all || unfold.names.contains s then
            if let some e' ← unfoldDefinition? e then
              unfold.used.modify (·.insert s)
              return ← reifyBracket atoms unfold e'
  let binary (ctor : Name) (a b : Expr) : MetaM Expr := do
    return mkApp2 (mkConst ctor) (← reifyBracket atoms unfold a) (← reifyBracket atoms unfold b)
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some k => return mkApp (mkConst ``CExpr.nat) (mkNatLit k)
    | none => throwError "bracket: {e} is not a numeral"
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => binary ``CExpr.add a b
  | (``HSub.hSub, #[_, _, _, _, a, b]) => binary ``CExpr.sub a b
  | (``HMul.hMul, #[_, _, _, _, a, b]) => binary ``CExpr.mul a b
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => binary ``CExpr.div a b
  | (``Neg.neg, #[_, _, a]) => return mkApp (mkConst ``CExpr.neg) (← reifyBracket atoms unfold a)
  | (``HPow.hPow, #[_, ty, _, _, a, n]) =>
    unless ← isDefEq ty (mkConst ``Nat) do
      throwError "bracket: the exponent of {e} is not a natural number"
    return mkApp2 (mkConst ``CExpr.pow) (← reifyBracket atoms unfold a) n
  | (``Real.sqrt, #[a]) => return mkApp (mkConst ``CExpr.sqrt) (← reifyBracket atoms unfold a)
  | (``Rat.cast, #[_, _, q]) => return mkApp (mkConst ``CExpr.rat) (← mkRatLit (← ratOfExpr q))
  | (``Min.min, #[_, _, a, b]) => binary ``CExpr.min a b
  | (``Max.max, #[_, _, a, b]) => binary ``CExpr.max a b
  | (c, _) =>
    -- An atom up to definitional equality: instance arguments may differ in their proof terms.
    for i in [0:atoms.size] do
      if ← isDefEq atoms[i]! e then return mkApp (mkConst ``CExpr.var) (mkNatLit i)
    unless unfold.all || unfold.names.contains c do
      throwError "bracket: {e} is not built from numerals, atoms, field operations, natural \
        powers, Real.sqrt, min and max; add its head constant {c} to the unfolding list"
    match ← unfoldDefinition? e with
    | some e' =>
      unfold.used.modify (·.insert c)
      reifyBracket atoms unfold e'
    | none => throwError "bracket: cannot unfold {c}"

/-- The atom and its rational bounds from a hypothesis `lo ≤ v ∧ v ≤ hi` or `v ∈ Set.Icc lo hi`. -/
def atomOfBound (ty : Expr) : MetaM (Expr × ℚ × ℚ) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``And, #[l, r]) =>
    match l.getAppFnArgs, r.getAppFnArgs with
    | (``LE.le, #[_, _, lo, v]), (``LE.le, #[_, _, v', hi]) =>
      unless v == v' do throwError "bracket: the two bounds of {ty} are about different terms"
      return (v, ← ratOfExpr lo, ← ratOfExpr hi)
    | _, _ => throwError "bracket: hypothesis {ty} is not of the form lo ≤ v ∧ v ≤ hi"
  | (``Membership.mem, #[_, _, _, s, v]) =>
    match s.getAppFnArgs with
    | (``Set.Icc, #[_, _, lo, hi]) => return (v, ← ratOfExpr lo, ← ratOfExpr hi)
    | _ => throwError "bracket: hypothesis {ty} is not of the form v ∈ Set.Icc lo hi"
  | _ => throwError "bracket: hypothesis {ty} is not of the form lo ≤ v ∧ v ≤ hi"

/-- The term `v` that a hypothesis `lo ≤ v ∧ v ≤ hi` bounds. -/
def boundedTerm {lo hi v : ℝ} (_ : lo ≤ v ∧ v ≤ hi) : ℝ := v

unsafe def encloseUnsafe (p : ℕ) (box ce : Expr) : MetaM (Option QInterval) := do
  let ty := mkApp (mkConst ``Option [Level.zero]) (mkConst ``QInterval)
  evalExpr (Option QInterval) ty (mkApp3 (mkConst ``CExpr.enclose) (mkNatLit p) box ce)

/-- The enclosure of a reified expression over a box at precision `p`, by compiled code. -/
@[implemented_by encloseUnsafe]
opaque enclose (p : ℕ) (box ce : Expr) : MetaM (Option QInterval)

/-- `x` rounded down to `d` decimal digits. -/
def decimalDown (d : ℕ) (x : ℚ) : ℚ := ((x * 10 ^ d).floor : ℚ) / 10 ^ d

/-- `x` rounded up to `d` decimal digits. -/
def decimalUp (d : ℕ) (x : ℚ) : ℚ := ((x * 10 ^ d).ceil : ℚ) / 10 ^ d

/-- A numeral term `n / d` (with a sign) for the rational number `q`, at the type `ty`. -/
def rationalSyntax (q : ℚ) (ty : TSyntax `term) : MacroM (TSyntax `term) := do
  let num := Syntax.mkNumLit (toString q.num.natAbs)
  let den := Syntax.mkNumLit (toString q.den)
  let magnitude ← if q.den = 1 then `(($num : $ty)) else `((($num : $ty) / $den))
  if q.num < 0 then `((-$magnitude)) else pure magnitude

/-- Options of `bracket`: the binary precision of the interval evaluation and the decimal digits
of the stated bounds. -/
declare_syntax_cat bracketOption
syntax " (" &"precision" " := " num ")" : bracketOption
syntax " (" &"digits" " := " num ")" : bracketOption

/-- The constants that the bracket commands unfold: a list, or `*` for every definition met. -/
declare_syntax_cat bracketUnfolds
syntax "[" ident,* "]" : bracketUnfolds
syntax "*" : bracketUnfolds

/-- The listed constants of an unfolding specification and whether it is `*`. -/
def readUnfolds (stx : Syntax) : CommandElabM (Array Name × Bool) := do
  if stx.getNumArgs == 1 then return (#[], true)
  let names ← liftCoreM <| stx[1].getSepArgs.mapM fun i => realizeGlobalConstNoOverloadWithInfo i
  return (names, false)

/-- A fresh unfolding of the listed constants, or of every definition. -/
def Unfolding.mk' (names : Array Name) (all : Bool) : MetaM Unfolding := do
  return ⟨names, all, ← IO.mkRef {}⟩

/-- The constants to unfold in the proof: the listed ones and those the reifier unfolded. -/
def Unfolding.lemmas (u : Unfolding) : MetaM (Array Name) := do
  let used ← u.used.get
  return u.names ++ (used.toList.filter (!u.names.contains ·)).toArray

/-- `bracket name : e using [h₁, …, hₘ] unfolding [c₁, …, cₖ]` proves
`name : lo ≤ e ∧ e ≤ hi` for a real expression `e`; with `via h` for `h : e = e'`, the enclosure
is computed for `e'`. The terms bounded by the hypotheses
`hⱼ : loⱼ ≤ vⱼ ∧ vⱼ ≤ hiⱼ` (or `vⱼ ∈ Set.Icc loⱼ hiⱼ`) are atoms; the constants `cᵢ` are unfolded
until `e` is built from numerals, atoms, the field operations, natural powers, `Real.sqrt`, `min`
and `max`; `unfolding *` unfolds every definition that is not an atom. The bounds are the interval
enclosure at binary precision `p` (default 64), rounded outward to `d` decimal digits (default 8) and
at least one unit of the last digit apart; the kernel checks the enclosure and
`CExpr.enclose_sound` proves that it contains `e`. -/
syntax (name := bracketCmd) (docComment)? "bracket " ident (bracketOption)* " : " term
  (" via " term)? (" using " "[" term,* "]")? " unfolding " bracketUnfolds : command

/-- Reads the `precision` and `digits` options of `bracket` and `bracket_up`. -/
def bracketOptions (options : Array Syntax) : CommandElabM (ℕ × ℕ) := do
  let mut precision : ℕ := 64
  let mut digits : ℕ := 8
  for option in options do
    let value ← match option[3].isNatLit? with
      | some v => pure v
      | none => throwError "bracket: option {option} has no numeral value"
    match option[1].getAtomVal with
    | "precision" => precision := value
    | "digits" => digits := value
    | other => throwError "bracket: unknown option {other}"
  return (precision, digits)

/-- Elaborates the theorem `name : lo ≤ e ∧ e ≤ hi` of `bracket` and returns its bounds. -/
def bracketTheorem (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (name : Ident)
    (e : Term) (via? : Option Term) (hyps : Array Term) (unfolds : Syntax)
    (precision digits : ℕ) : CommandElabM (ℚ × ℚ) := do
  let (unfoldNames, all) ← readUnfolds unfolds
  let exprName := (← getCurrNamespace) ++ name.getId ++ `cexpr
  let (ce, boxes, enclosure, unfolded) ← liftTermElabM do
    let spec ← Unfolding.mk' unfoldNames all
    let mut atoms : Array Expr := #[]
    let mut boxes : Array (ℚ × ℚ) := #[]
    for h in hyps do
      let he ← elabTerm h none
      synthesizeSyntheticMVarsNoPostponing
      let (v, lo, hi) ← atomOfBound (← inferType he)
      atoms := atoms.push v
      boxes := boxes.push (lo, hi)
    let ee ← elabTerm e (some (mkConst ``Real))
    synthesizeSyntheticMVarsNoPostponing
    -- With `via h : e = e'`, the expression evaluated is `e'`.
    let ee ← match via? with
      | none => instantiateMVars ee
      | some hv => do
        let ty ← instantiateMVars (← inferType (← elabTerm hv none))
        let some (_, lhs, rhs) := ty.eq?
          | throwError "bracket: {ty} is not an equation"
        unless ← isDefEq lhs ee do throwError "bracket: the left side of {ty} is not {ee}"
        instantiateMVars rhs
    let ce ← reifyBracket atoms spec ee
    let boxExprs ← boxes.mapM fun (lo, hi) => do
      return mkApp2 (mkConst ``QInterval.mk) (← mkRatLit lo) (← mkRatLit hi)
    let box ← mkListLit (mkConst ``QInterval) boxExprs.toList
    return (ce, boxes, ← enclose precision box ce, ← spec.lemmas)
  let some I := enclosure
    | throwError "bracket: a divisor's enclosure contains zero at precision {precision}"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := exprName, levelParams := [], type := mkConst ``CExpr, value := ce,
    hints := .abbrev, safety := .safe }
  -- A one-point enclosure is widened by a unit of the last digit, so that every bracket bounds its
  -- term by an interval of positive width, as the Bernstein tests require of their variables.
  let lo₀ := decimalDown digits I.lo
  let hi₀ := decimalUp digits I.hi
  let (lo, hi) := if lo₀ = hi₀ then (lo₀ - 1/10^digits, hi₀ + 1/10^digits) else (lo₀, hi₀)
  let realTy ← `(ℝ)
  let ratTy ← `(ℚ)
  let loReal ← liftMacroM <| rationalSyntax lo realTy
  let hiReal ← liftMacroM <| rationalSyntax hi realTy
  let loRat ← liftMacroM <| rationalSyntax lo ratTy
  let hiRat ← liftMacroM <| rationalSyntax hi ratTy
  let mut boxTerms : Array Term := #[]
  for (blo, bhi) in boxes do
    let bloRat ← liftMacroM <| rationalSyntax blo ratTy
    let bhiRat ← liftMacroM <| rationalSyntax bhi ratTy
    boxTerms := boxTerms.push (← `(Cycle63.Certificate.QInterval.mk $bloRat $bhiRat))
  -- The atoms, written as the terms the hypotheses bound: `(h).1 : lo ≤ v` names `v` by its type.
  let atomTerms : Array Term ← hyps.mapM fun h => `((Cycle63.Certificate.boundedTerm ($h)))
  let atomList ← `([$atomTerms,*])
  let boxList ← `([$boxTerms,*])
  -- The box condition: each atom lies in its interval, from the hypothesis about it.
  let mut boxProof ← `(Cycle63.Certificate.CExpr.inBoxes_nil (Cycle63.Certificate.CExpr.ptOfList []))
  for h in hyps.reverse do
    boxProof ← `(Cycle63.Certificate.CExpr.inBoxes_cons
      ⟨le_trans (le_of_eq (by norm_num)) ($h).1, le_trans ($h).2 (le_of_eq (by norm_num))⟩
      $boxProof)
  let exprId := mkIdent exprName
  let prec := Syntax.mkNumLit (toString precision)
  let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    unfolded.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):ident)
  let rewriteVia ← match via? with
    | none => `(tactic| skip)
    | some hv => `(tactic| rw [$hv:term])
  elabCommand (← `(command|
    $[$doc?:docComment]? theorem $name : $loReal ≤ $e ∧ $e ≤ $hiReal := by
      have hden : Cycle63.Certificate.CExpr.denote (Cycle63.Certificate.CExpr.ptOfList $atomList)
          $exprId = $e := by
        $rewriteVia:tactic
        delta $exprId:ident
        simp only [Cycle63.Certificate.CExpr.denote, Cycle63.Certificate.CExpr.ptOfList,
          Cycle63.Certificate.boundedTerm, List.getD_cons_zero, List.getD_cons_succ, $lemmas,*] <;>
          push_cast <;> first | with_reducible rfl | ring_nf
      obtain ⟨hlo, hhi⟩ := Cycle63.Certificate.CExpr.bounds_of_within $prec $boxList $exprId $loRat
        $hiRat (by decide +kernel) (Cycle63.Certificate.CExpr.ptOfList $atomList) $boxProof
      rw [hden] at hlo hhi
      have hloCast : (($loRat : ℚ) : ℝ) = $loReal := by norm_num
      have hhiCast : (($hiRat : ℚ) : ℝ) = $hiReal := by norm_num
      rw [hloCast] at hlo
      rw [hhiCast] at hhi
      exact ⟨hlo, hhi⟩))
  return (lo, hi)

@[command_elab bracketCmd] def elabBracket : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs = 0 then none else some ⟨stx[0][0]⟩
  let via? : Option Term := if stx[6].getNumArgs = 0 then none else some ⟨stx[6][1]⟩
  let hyps : Array Term := if stx[7].getNumArgs = 0 then #[] else stx[7][2].getSepArgs.map (⟨·⟩)
  let (precision, digits) ← bracketOptions stx[3].getArgs
  discard <| bracketTheorem doc? ⟨stx[2]⟩ ⟨stx[5]⟩ via? hyps stx[9] precision digits

/-- `bracket_up name : e using [h₁, …] unfolding [c₁, …]` defines `name` as the upper end `hi` of
the enclosure of `e` that `bracket` computes, rounded up to `d` decimal digits (option `digits`,
default 8): it proves `name_enclosure : lo ≤ e ∧ e ≤ hi`, defines `name : ℝ := hi` and proves
`name_ge : e ≤ name`. -/
syntax (name := bracketUpCmd) (docComment)? "bracket_up " ident (bracketOption)* " : " term
  (" using " "[" term,* "]")? " unfolding " bracketUnfolds : command

@[command_elab bracketUpCmd] def elabBracketUp : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs = 0 then none else some ⟨stx[0][0]⟩
  let name : Ident := ⟨stx[2]⟩
  let e : Term := ⟨stx[5]⟩
  let hyps : Array Term := if stx[6].getNumArgs = 0 then #[] else stx[6][2].getSepArgs.map (⟨·⟩)
  let (precision, digits) ← bracketOptions stx[3].getArgs
  let enclosureName := mkIdent (name.getId.appendAfter "_enclosure")
  let (_, hi) ← bracketTheorem none enclosureName e none hyps stx[8] precision digits
  let hiReal ← liftMacroM <| rationalSyntax hi (← `(ℝ))
  let geName := mkIdent (name.getId.appendAfter "_ge")
  elabCommand (← `(command| $[$doc?:docComment]? noncomputable def $name : ℝ := $hiReal))
  elabCommand (← `(command|
    theorem $geName : $e ≤ $name := by
      unfold $name:ident
      exact ($enclosureName).2))

end Cycle63.Certificate

end Record1252270103Bootstrap.PR67
