import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Bracket
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The `bracket_argmin` command: defines a numeral as the point of an interval at which a real
function is smallest, found at elaboration time by golden-section search with the interval
evaluation of `Cycle63.Certificate.Interval`. Released under Apache 2.0. -/
set_option autoImplicit false

open Lean Meta Elab Command Term

namespace Cycle63.Certificate

unsafe def cexprOfExprUnsafe (ce : Expr) : MetaM CExpr := evalExpr CExpr (mkConst ``CExpr) ce

/-- The value of a `CExpr` term, by compiled code. -/
@[implemented_by cexprOfExprUnsafe]
opaque cexprOfExpr (ce : Expr) : MetaM CExpr

/-- The floating-point value of a rational number. -/
def ratToFloat (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- The `n`-th power of a floating-point number by repeated multiplication, which IEEE arithmetic
rounds the same way on every machine. -/
def floatPow (x : Float) : ℕ → Float
  | 0 => 1
  | n + 1 => floatPow x n * x

/-- The floating-point value of `ce` with the variable `i` at `x i`. -/
def CExpr.floatValue (x : ℕ → Float) : CExpr → Float
  | .nat n => Float.ofNat n
  | .rat q => ratToFloat q
  | .var i => x i
  | .add a b => a.floatValue x + b.floatValue x
  | .sub a b => a.floatValue x - b.floatValue x
  | .mul a b => a.floatValue x * b.floatValue x
  | .div a b => a.floatValue x / b.floatValue x
  | .neg a => -a.floatValue x
  | .pow a n => floatPow (a.floatValue x) n
  | .sqrt a => Float.sqrt (a.floatValue x)
  | .min a b => Min.min (a.floatValue x) (b.floatValue x)
  | .max a b => Max.max (a.floatValue x) (b.floatValue x)

/-- The floating-point value of `ce` with the variable `0` at the point `t` and the atoms at the
midpoints of their intervals. -/
def floatValueAt (atoms : List QInterval) (ce : CExpr) (t : ℚ) : Float :=
  let points := (t :: atoms.map fun I => (I.lo + I.hi)/2).map ratToFloat
  ce.floatValue fun i => points.getD i 0

/-- Elaborates a search command `cmd name (options) : f on a b using [h₁, …] unfolding [c₁, …]`: reifies `f`
with the atoms bounded by the hypotheses `hⱼ`, runs `search` on the floating-point values of `f` over
`[a, b]` with the option `digits` (default 6), and defines `name` as the point it returns, with
`name_mem : a ≤ name ∧ name ≤ b`. -/
def elabSearchCommand (cmd : String)
    (search : (ℚ → TermElabM Float) → ℚ → ℚ → ℕ → TermElabM ℚ) : CommandElab := fun stx => do
  let doc? : Option (TSyntax ``Lean.Parser.Command.docComment) :=
    if stx[0].getNumArgs = 0 then none else some ⟨stx[0][0]⟩
  let name : Ident := ⟨stx[2]⟩
  let f : Term := ⟨stx[5]⟩
  let aStx : Term := ⟨stx[7]⟩
  let bStx : Term := ⟨stx[8]⟩
  let hyps : Array Term := if stx[9].getNumArgs = 0 then #[] else stx[9][2].getSepArgs.map (⟨·⟩)
  let (unfoldNames, all) ← readUnfolds stx[11]
  let mut digits : ℕ := 6
  for option in stx[3].getArgs do
    let value ← match option[3].isNatLit? with
      | some v => pure v
      | none => throwError "{cmd}: option {option} has no numeral value"
    match option[1].getAtomVal with
    | "digits" => digits := value
    | other => throwError "{cmd}: unknown option {other}"
  let point ← liftTermElabM do
    let spec ← Unfolding.mk' unfoldNames all
    let mut atoms : List QInterval := []
    let mut atomExprs : Array Expr := #[]
    for h in hyps do
      let he ← elabTerm h none
      synthesizeSyntheticMVarsNoPostponing
      let (v, vlo, vhi) ← atomOfBound (← inferType he)
      atomExprs := atomExprs.push v
      atoms := atoms ++ [⟨vlo, vhi⟩]
    let fe ← elabTerm f (some (← mkArrow (mkConst ``Real) (mkConst ``Real)))
    synthesizeSyntheticMVarsNoPostponing
    let fe ← instantiateMVars fe
    let a ← ratOfExpr (← elabTerm aStx (some (mkConst ``Real)))
    let b ← ratOfExpr (← elabTerm bStx (some (mkConst ``Real)))
    let ce ← withLocalDeclD `t (mkConst ``Real) fun t =>
      reifyBracket (#[t] ++ atomExprs) spec (mkApp fe t).headBeta
    let ce ← cexprOfExpr ce
    let value (t : ℚ) : TermElabM Float := do
      let v := floatValueAt atoms ce t
      if v.isNaN || v.isInf then throwError "{cmd}: the value at {t} is not a finite number"
      return v
    let r ← search value a b digits
    unless a ≤ r ∧ r ≤ b do throwError "{cmd}: the point {r} lies outside [{a}, {b}]"
    return r
  let pointReal ← liftMacroM <| rationalSyntax point (← `(ℝ))
  let memName := mkIdent (name.getId.appendAfter "_mem")
  elabCommand (← `(command| $[$doc?:docComment]? noncomputable def $name : ℝ := $pointReal))
  elabCommand (← `(command|
    theorem $memName : ($aStx : ℝ) ≤ $name ∧ $name ≤ $bStx := by
      unfold $name:ident
      constructor <;> norm_num))

/-- The point of `[a, b]` that golden-section search finds for the smallest value, rounded to `digits`
decimal digits. The search points lie on a grid finer than the result, so that the rationals stay small. -/
def goldenSearch (value : ℚ → TermElabM Float) (a b : ℚ) (digits : ℕ) : TermElabM ℚ := do
  let grid : ℚ := 1/10^(digits + 6)
  let snap (t : ℚ) : ℚ := decimalDown (digits + 6) t
  let golden : ℚ := 6180339887498949/10^16
  let mut lo := a
  let mut hi := b
  let mut c := snap (hi - golden*(hi - lo))
  let mut d := snap (lo + golden*(hi - lo))
  let mut fc ← value c
  let mut fd ← value d
  while hi - lo > 100*grid do
    if fc < fd then
      hi := d; d := c; fd := fc
      c := snap (hi - golden*(hi - lo)); fc ← value c
    else
      lo := c; c := d; fc := fd
      d := snap (lo + golden*(hi - lo)); fd ← value d
  return decimalDown digits ((lo + hi)/2 + 1/(2*10^digits))

/-- The point of `[a, b]` at which bisection finds the value change sign from negative at `a` to
nonnegative at `b`, rounded up to `digits` decimal digits. -/
def crossingSearch (value : ℚ → TermElabM Float) (a b : ℚ) (digits : ℕ) : TermElabM ℚ := do
  unless (← value a) < 0 && 0 ≤ (← value b) do
    throwError "bracket_crossing: the value is not negative at {a} and nonnegative at {b}"
  let grid : ℚ := 1/10^(digits + 6)
  let snap (t : ℚ) : ℚ := decimalDown (digits + 6) t
  let mut lo := a
  let mut hi := b
  while hi - lo > 100*grid do
    let mid := snap ((lo + hi)/2)
    if (← value mid) < 0 then lo := mid else hi := mid
  return decimalUp digits hi

/-- `bracket_argmin name : f on a b using [h₁, …] unfolding [c₁, …]` defines `name : ℝ` as the point
of `[a, b]`, rounded to `d` decimal digits (option `digits`, default 6), that golden-section search
finds for the smallest value of `f : ℝ → ℝ`, where `f t`, after unfolding the constants `cᵢ` (every
definition with `unfolding *`), is built from numerals, `t`, the atoms bounded by the hypotheses `hⱼ`,
the field operations, natural powers, `Real.sqrt`, `min` and `max`. The search compares
floating-point values of `f`, with the atoms at the midpoints of their bounds. It proves
`name_mem : a ≤ name ∧ name ≤ b`. The search assumes that `f` has one minimum on `[a, b]`; that the
point is a minimizer is a separate certificate. -/
syntax (name := bracketArgminCmd) (docComment)? "bracket_argmin " ident (bracketOption)* " : " term
  " on " term:max term:max (" using " "[" term,* "]")? " unfolding " bracketUnfolds : command

@[command_elab bracketArgminCmd] def elabBracketArgmin : CommandElab :=
  elabSearchCommand "bracket_argmin" goldenSearch

/-- `bracket_crossing name : f on a b using [h₁, …] unfolding [c₁, …]` defines `name : ℝ` as the point
of `[a, b]` at which bisection finds that `f` changes sign from negative at `a` to nonnegative at `b`,
rounded up to `d` decimal digits (option `digits`, default 6), with `f` and its atoms as for
`bracket_argmin`. It proves `name_mem : a ≤ name ∧ name ≤ b`; the sign of `f` at the point is a separate
certificate. -/
syntax (name := bracketCrossingCmd) (docComment)? "bracket_crossing " ident (bracketOption)* " : " term
  " on " term:max term:max (" using " "[" term,* "]")? " unfolding " bracketUnfolds : command

@[command_elab bracketCrossingCmd] def elabBracketCrossing : CommandElab :=
  elabSearchCommand "bracket_crossing" crossingSearch

end Cycle63.Certificate

end Record1252270103Bootstrap.PR67
