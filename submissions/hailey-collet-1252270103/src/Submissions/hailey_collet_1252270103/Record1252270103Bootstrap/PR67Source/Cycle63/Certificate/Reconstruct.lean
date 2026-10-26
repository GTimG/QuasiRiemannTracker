import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Certificate.Reduction
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
/- The reduced fraction of a rational expression, found at elaboration time by exact linear algebra
on its values at integer points: for each variable the smallest total degree of a quotient that
takes the values along it, then the coefficients of the quotient in all variables as the null
vector of an integer matrix. The kernel never sees this computation; it checks the result.
Released under Apache 2.0. -/
set_option autoImplicit false

namespace Cycle63.Certificate

namespace Reconstruct

/-- A polynomial: monomials as exponent vectors with their coefficients. -/
abbrev Poly := Array (Array ℕ × ℚ)

/-- The monomial `∏ xᵢ ^ αᵢ` at a point. -/
def monomialAt (α : Array ℕ) (pt : Array ℚ) : ℚ := Id.run do
  let mut m : ℚ := 1
  for i in [0:α.size] do
    m := m * pt[i]! ^ α[i]!
  return m

/-- All exponent vectors bounded by `deg` componentwise. -/
def exponents (deg : Array ℕ) : Array (Array ℕ) := Id.run do
  let mut out : Array (Array ℕ) := #[#[]]
  for d in deg do
    let mut next : Array (Array ℕ) := #[]
    for α in out do
      for k in [0:d + 1] do
        next := next.push (α.push k)
    out := next
  return out

/-- The value of the expression at a point with integer coordinates, when the denominator of its
fraction does not vanish there. -/
def valueAt (e : RatExpr) (pt : Array ℚ) : Option ℚ :=
  match RatExpr.fracAt (fun i => (pt.getD i 0).floor) e with
  | (n, d) => if d = 0 then none else some ((n : ℚ) / d)

/-- A row echelon form by fraction-free elimination, in which every entry stays an integer, with
the pivot positions. -/
def echelon (rows : Array (Array ℤ)) (ncols : ℕ) : Array (Array ℤ) × Array (ℕ × ℕ) := Id.run do
  let mut a := rows
  let mut prev : ℤ := 1
  let mut r := 0
  let mut pivots : Array (ℕ × ℕ) := #[]
  for c in [0:ncols] do
    if r < a.size then
      let mut piv : Option ℕ := none
      for i in [r:a.size] do
        if piv.isNone && (a[i]!)[c]! ≠ 0 then piv := some i
      if let some i := piv then
        let rowI := a[i]!
        a := (a.set! i a[r]!).set! r rowI
        let p := rowI[c]!
        for k in [r + 1:a.size] do
          let rowK := a[k]!
          let f := rowK[c]!
          a := a.set! k ((Array.range ncols).map fun j =>
            if j < c then rowK[j]! else if j = c then 0 else (p * rowK[j]! - f * rowI[j]!) / prev)
        prev := p
        pivots := pivots.push (r, c)
        r := r + 1
  return (a, pivots)

/-- A nonzero vector of the null space of an integer matrix. -/
def nullVector (rows : Array (Array ℤ)) (ncols : ℕ) : Option (Array ℚ) := Id.run do
  let (a, pivots) := echelon rows ncols
  let pivotCols := pivots.map (·.2)
  let some free := (Array.range ncols).find? (fun c => !pivotCols.contains c) | return none
  let mut v : Array ℚ := Array.replicate ncols 0
  v := v.set! free 1
  for k in (List.range pivots.size).reverse do
    let (r, c) := pivots[k]!
    let row := a[r]!
    let mut s : ℚ := 0
    for j in [c + 1:ncols] do
      s := s + (row[j]! : ℚ) * v[j]!
    v := v.set! c (-s / (row[c]! : ℚ))
  return some v

/-- The values of the expression at the points where the denominator of its fraction does not
vanish. -/
def samplesAt (e : RatExpr) (points : Array (Array ℚ)) : Array (Array ℚ × ℚ) :=
  points.filterMap fun pt => (valueAt e pt).map (pt, ·)

/-- The polynomial at a point. -/
def evalPoly (F : Poly) (pt : Array ℚ) : ℚ := F.foldl (fun acc (α, c) => acc + c * monomialAt α pt) 0

/-- The fraction `P/Q` with the given degree bounds that takes the sampled values at integer
points, checked at the extra samples. -/
def solveWith (degP degQ : Array ℕ) (samples extra : Array (Array ℚ × ℚ)) :
    Option (Poly × Poly) := Id.run do
  let monsP := exponents degP
  let monsQ := exponents degQ
  let rows : Array (Array ℤ) := samples.map fun (pt, y) =>
    monsP.map (fun α => (y.den : ℤ) * (monomialAt α pt).num) ++
      monsQ.map fun α => -y.num * (monomialAt α pt).num
  let some v := nullVector rows (monsP.size + monsQ.size) | return none
  let P : Poly := (Array.range monsP.size).filterMap fun (j : ℕ) =>
    if (v[j]! : ℚ) = 0 then none else some ((monsP[j]!, v[j]!) : Array ℕ × ℚ)
  let Q : Poly := (Array.range monsQ.size).filterMap fun (j : ℕ) =>
    if (v[monsP.size + j]! : ℚ) = 0 then none
    else some ((monsQ[j]!, v[monsP.size + j]!) : Array ℕ × ℚ)
  if Q.isEmpty then return none
  for (pt, y) in samples ++ extra do
    if evalPoly P pt ≠ y * evalPoly Q pt then return none
  return some (P, Q)

/-- An integer hash with the avalanche property: every input bit affects every output bit. -/
def mix (a : ℕ) : ℕ := Id.run do
  let mut x := a % 4294967296
  x := ((x ^^^ (x >>> 16)) * 73244475) % 4294967296
  x := ((x ^^^ (x >>> 16)) * 73244475) % 4294967296
  return x ^^^ (x >>> 16)

/-- A pseudo-random integer coordinate in `[1, 61]`, independent across coordinates: coordinate
`i` of the `j`-th point. -/
def scatter (i j : ℕ) : ℚ := ((mix (j * 1000003 + i * 7919 + 1) % 61 + 1 : ℕ) : ℚ)

/-- The degrees of the reduced fraction along the variable `i`, the others fixed at generic
integers: the smallest total degree with a solution. -/
def degreesAlong (e : RatExpr) (nvars i maxTotal : ℕ) : Option (ℕ × ℕ) := Id.run do
  let base : Array ℚ := (Array.range nvars).map fun v => ((5 * v + 7 : ℕ) : ℚ)
  let along (j : ℕ) : Array ℚ := base.set! i ((j + 1 : ℕ) : ℚ)
  let samples := samplesAt e ((Array.range (maxTotal + 4)).map along)
  let extra := samplesAt e ((Array.range 4).map fun j => along (maxTotal + 10 + j))
  for total in [0:maxTotal + 1] do
    if total + 3 ≤ samples.size then
      for m in [0:total + 1] do
        let degP := (Array.replicate nvars 0).set! i m
        let degQ := (Array.replicate nvars 0).set! i (total - m)
        if let some (P, Q) := solveWith degP degQ (samples.extract 0 (total + 3)) extra then
          let degOf (F : Poly) : ℕ := F.foldl (fun acc (α, _) => max acc α[i]!) 0
          return some (degOf P, degOf Q)
  return none

/-- The reduced fraction of the expression in `nvars` variables, by exact linear algebra on values
at integer points, with integer coefficients without a common factor. -/
def reduce (e : RatExpr) (nvars maxTotal : ℕ) : Option (Poly × Poly) := Id.run do
  let mut degP : Array ℕ := #[]
  let mut degQ : Array ℕ := #[]
  for i in [0:nvars] do
    let some (m, n) := degreesAlong e nvars i maxTotal | return none
    degP := degP.push m
    degQ := degQ.push n
  let unknowns := (exponents degP).size + (exponents degQ).size
  let point (j : ℕ) : Array ℚ := (Array.range nvars).map fun i => scatter i j
  let samples := samplesAt e ((Array.range (unknowns + 8)).map point)
  let extra := samplesAt e ((Array.range 6).map fun j => point (unknowns + 40 + j))
  let some (P, Q) := solveWith degP degQ samples extra | return none
  let dens : ℕ := (P ++ Q).foldl (fun (acc : ℕ) (mono : Array ℕ × ℚ) => Nat.lcm acc mono.2.den) 1
  let nums : ℕ := (P ++ Q).foldl
    (fun (acc : ℕ) (mono : Array ℕ × ℚ) => Nat.gcd acc (mono.2 * dens).num.natAbs) 0
  let scale : ℚ := (dens : ℚ) / (nums : ℚ)
  return some (P.map fun (α, c) => (α, c * scale), Q.map fun (α, c) => (α, c * scale))

end Reconstruct

end Cycle63.Certificate

end Record1252270103Bootstrap.PR67
