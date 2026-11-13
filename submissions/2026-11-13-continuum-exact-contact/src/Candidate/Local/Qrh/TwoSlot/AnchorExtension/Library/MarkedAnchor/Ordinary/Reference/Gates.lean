/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Scalar part of the reference lane: the explicit per-stage hypotheses on the step data, the
reflected rectangle inside the parent face `G(.99, 49/20, .14)` (the reflection gate, also after
a forward-kernel shortening `t₂` paid by frozen marks `f` and erased live width `e`), and the
tilt arithmetic of the forward kernel. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.Reference.Parent
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.StepData

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.Reference
noncomputable section
open QRH.Record12518109Source QRH.Record1252270103Source

/-- **Explicit scalar hypotheses of the reference lane on the step data** (checked per stage
from the chain data).
* `lref = 7/50`, `alpha = 3/5`, `Pref = 2/3`;
* `ρ` is the reflection-gate reserve at the worst lane root (`P = Pref`, `S = c`, short width `lref`):
  `1 - Pref + 2 lref + L_ref c + ρ ≤ B_ref`;
* the mark cap of the parent with the same reserve: `c + ρ ≤ c_ref`;
* the step face facts the reflection uses: `B ≤ 1` (so the reflected width `1 - P + x ≥ 0`). -/
structure RefGates (D : StepData) (ρ : ℝ) : Prop where
  lref : D.lref = 7/50
  alpha : D.alpha = 3/5
  Pref : D.Pref = 2/3
  reserve : 0 < ρ
  gate : 1 - D.Pref + 2*D.lref + Lref*D.c + ρ ≤ Bref
  cap : D.c + ρ ≤ cref
  B_le : D.B ≤ 1

/-- **The reflection gate on every lane root**, with its reserve: an original factor (or the reference
factor) of width `x ≤ lref`, the long factor of width `P - x` reflected to `1 - P + x`. -/
theorem gate_43 {D : StepData} {ρ : ℝ} (G : RefGates D ρ) {P S x : ℝ}
    (hP : D.Pref ≤ P) (hS : S ≤ D.c) (hx : x ≤ D.lref) :
    x + (1 - P + x) + Lref*S + ρ ≤ Bref := by
  have hL : (0:ℝ) ≤ Lref := by norm_num [Lref]
  have := G.gate
  nlinarith [mul_le_mul_of_nonneg_left hS hL]

/-- **The reflected rectangle lies in the parent face**, with an additive slack
`δ ≤ ρ` for the `o(1)` conductor/rounding losses of the reflected length (`Q_z ≤ C·Z`). -/
theorem reflected_admissible {D : StepData} {ρ : ℝ} (G : RefGates D ρ) {P S x δ : ℝ}
    (hP : D.Pref ≤ P) (hP1 : P ≤ 1) (hS0 : 0 ≤ S) (hS : S ≤ D.c) (hx0 : 0 ≤ x) (hx : x ≤ D.lref)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ρ) :
    (globalFace Bref Lref cref).Admissible x (1 - P + x + δ) S 1 := by
  have hL : (0:ℝ) ≤ Lref := by norm_num [Lref]
  have h43 := gate_43 G hP hS hx
  apply (globalFace_admissible_iff hx0 (by linarith) hS0 hL).mpr
  constructor
  · have := G.cap; linarith
  · linarith

/-- **Forward kernel after reflection**: shortening the long factor by an extracted
ordinary divisor of width `t₂` lengthens the reflected factor by `t₂`; the parent capacity defect
`t₂ - L_ref f` (frozen marks `f`) is paid by erasing live marked width `e` with
`L_ref (f + e) ≥ t₂`. The shortened, erased reflected rectangle is still in the parent face. -/
theorem kernel_admissible {D : StepData} {ρ : ℝ} (G : RefGates D ρ) {P S x δ t₂ f e : ℝ}
    (hP : D.Pref ≤ P) (hP1 : P ≤ 1) (hS : S ≤ D.c) (hx0 : 0 ≤ x) (hx : x ≤ D.lref)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ρ) (ht₂ : 0 ≤ t₂) (hf : 0 ≤ f) (he : 0 ≤ e)
    (hlive : 0 ≤ S - f - e) (hpay : t₂ ≤ Lref*(f + e)) :
    (globalFace Bref Lref cref).Admissible x (1 - P + x + t₂ + δ) (S - f - e) 1 := by
  have hL : (0:ℝ) ≤ Lref := by norm_num [Lref]
  have h43 := gate_43 G hP hS hx
  apply (globalFace_admissible_iff hx0 (by linarith) hlive hL).mpr
  constructor
  · have := G.cap; linarith
  · nlinarith

/-- The native squared prime cost of erasing live slots. -/
def kappaStar : ℝ := 3/4
/-- The Hilbert-norm tilt `r₀ = κ*/(2 L_ref)`. -/
def r0 : ℝ := kappaStar/(2*Lref)

theorem r0_eq : r0 = 15/98 := by norm_num [r0, kappaStar, Lref]

/-- The energy cost `(κ*/L_ref)(t₂ - L_ref f)` of the erasure is twice the tilt. -/
theorem erasure_cost (t₂ f : ℝ) :
    kappaStar/Lref*(t₂ - Lref*f) = 2*(r0*t₂ - r0*Lref*f) := by
  unfold r0 kappaStar Lref; ring

/-- The tilted ordinary-only prime exponent `3(1/2 - r₀) = 51/49 > 1`. -/
theorem tilted_ordinary_exponent : 3*(1/2 - r0) = 51/49 ∧ (1:ℝ) < 3*(1/2 - r0) := by
  rw [r0_eq]; norm_num

/-- The worst exponent of a frozen marked prime with `m` labels and ordinary degree `k`,
after summing its prime pool. -/
def primeExponent (k m : ℕ) : ℝ := 1 - ((k:ℝ) + m)/2 + r0*((k:ℝ) - Lref*m)

/-- The prime exponent for `m = 1`, `k ≥ 1`: `r₀(1 - L_ref) + (k-1)(r₀ - 1/2)`. -/
theorem primeExponent_one (k : ℕ) :
    primeExponent k 1 = r0*(1 - Lref) + ((k:ℝ) - 1)*(r0 - 1/2) := by
  unfold primeExponent; push_cast; ring

/-- **Every forward-kernel prime has a negative exponent**, uniformly `≤ -2/49`:
ordinary-only terms (`m = 0`, `k ≥ 3`), single marks with ordinary degree (`m = 1`, `k ≥ 1`) and
collisions (`m ≥ 2`, any `k`). -/
theorem primeExponent_neg (k m : ℕ)
    (h : (m = 0 ∧ 3 ≤ k) ∨ (m = 1 ∧ 1 ≤ k) ∨ 2 ≤ m) :
    primeExponent k m ≤ -2/49 := by
  have hr : r0 = 15/98 := r0_eq
  unfold primeExponent
  rw [hr]
  simp only [Lref]
  rcases h with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | hm
  · have : (3:ℝ) ≤ k := by exact_mod_cast hk
    push_cast; nlinarith
  · have : (1:ℝ) ≤ k := by exact_mod_cast hk
    push_cast; nlinarith
  · have : (2:ℝ) ≤ m := by exact_mod_cast hm
    have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

/-- `exp(r₀ x₊) ≤ 1 + exp(r₀ x)`, for any nonnegative tilt. -/
theorem exp_pos_part_le (r x : ℝ) (_hr : 0 ≤ r) :
    Real.exp (r*max x 0) ≤ 1 + Real.exp (r*x) := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, mul_zero, Real.exp_zero]
    linarith [Real.exp_pos (r*x)]
  · rw [max_eq_left h]
    linarith

end
end Qrh.MarkedAnchor.Ordinary.Reference
