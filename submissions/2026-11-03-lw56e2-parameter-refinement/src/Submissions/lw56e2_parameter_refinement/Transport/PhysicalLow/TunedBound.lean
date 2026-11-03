/-
Historical contribution by LW56e2, Apache-2.0.
Source: https://github.com/LW56e2/quasi-riemann-improved
Commit: b83dbbd914c5751acf9bc3389cde58970437278f
Original path: lean/Transport/PhysicalLow/TunedBound.lean
Original SHA-256: 34592a794de5716856f55ad85cb829aec21dc9c519ee8faa9182d295d055b065
Tracker adaptation: import modules moved under Submissions.lw56e2_parameter_refinement;
OpenAI imports use the openai-baseline dependency; RH.Transport renamed LW56e2.Transport.
Original proof bodies and source attribution otherwise retained.
-/
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalLow.LowWindowBound
import Submissions.lw56e2_parameter_refinement.Transport.TunedCandidate
import Submissions.lw56e2_parameter_refinement.Transport.PhysicalHigh.DistinctSlots

/-!
# The actual low probe at the tuned parameters

This specializes the transported physical estimate; it does not postulate a
low estimate. At the proposed boundary the power is exactly the principal
signal power. A positive loss is therefore chosen only after beta > B.
The arbitrary distinct lengths below can be shared by the low, high, and
principal constructions. Source analytic definitions remain unchanged.
-/

namespace LW56e2.Transport.PhysicalLow
noncomputable section
open scoped Classical BigOperators ContDiff SchwartzMap
open Filter
open OAI OAI.SevenEighths
open ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem tuned_total_pos : 0 < TunedCandidate.ell := by
  norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]

theorem tuned_total_le : TunedCandidate.ell ≤ 1/5 := by
  norm_num [TunedCandidate.ell, Geometry.ell, TunedCandidate.p]

theorem tuned_width_sum : TunedCandidate.lx + TunedCandidate.ly = 1 - TunedCandidate.ell := by
  linarith [TunedCandidate.width_eq_sum, TunedCandidate.width_add_ell]

theorem tuned_xy_lt : TunedCandidate.lx < TunedCandidate.ly := by
  linarith [TunedCandidate.ly_eq, TunedCandidate.b_pos]

theorem tuned_source_growth : TunedCandidate.ell < 2*TunedCandidate.lx-TunedCandidate.ly := by
  rcases TunedCandidate.geometry_values with ⟨he,hx,hy,hh⟩
  rw [he,hx,hy]
  norm_num

theorem tuned_low_power : TunedCandidate.lx/2+(TunedCandidate.ly-TunedCandidate.lx)/12 = TunedCandidate.signal TunedCandidate.B := by
  rw [TunedCandidate.signal_boundary, TunedCandidate.ly_eq]
  dsimp [TunedCandidate.lowExponent, TunedCandidate.lowExponentAt, TunedCandidate.lx]
  ring

/-- The loss is positive only in the supremum contradiction regime. -/
def lowGap (beta : ℝ) : ℝ := min ((beta-TunedCandidate.B)/4) TunedCandidate.zeta

theorem lowGap_pos {beta : ℝ} (hbeta : TunedCandidate.B < beta) : 0 < lowGap beta := by
  exact lt_min (by linarith) TunedCandidate.zeta_pos

theorem lowGap_le_quarter (beta : ℝ) : lowGap beta ≤ (beta-TunedCandidate.B)/4 :=
  min_le_left _ _

theorem lowGap_le_zeta (beta : ℝ) : lowGap beta ≤ TunedCandidate.zeta := min_le_right _ _

theorem low_power_gap (beta : ℝ) :
    TunedCandidate.signal TunedCandidate.B + lowGap beta ≤ TunedCandidate.signal beta - 3*lowGap beta := by
  have hg := lowGap_le_quarter beta
  have hs := TunedCandidate.signal_difference beta TunedCandidate.B
  linarith

/-- A single fixed family, suitable for all three analytic sides. -/
def tunedSlots (K : ℕ) (hK : 0 < K) : Fin K → ℝ :=
  Classical.choose (PhysicalHigh.distinct_slots_for_size TunedCandidate.ell tuned_total_pos K hK)

theorem tunedSlots_spec (K : ℕ) (hK : 0 < K) :
    Function.Injective (tunedSlots K hK) ∧
    (∑ j, tunedSlots K hK j) = TunedCandidate.ell ∧
    (∀ j, TunedCandidate.ell/(2*K) ≤ tunedSlots K hK j ∧
      tunedSlots K hK j < 2*TunedCandidate.ell/K) :=
  Classical.choose_spec (PhysicalHigh.distinct_slots_for_size TunedCandidate.ell tuned_total_pos K hK)

theorem tunedSlots_pos (K : ℕ) (hK : 0 < K) (j : Fin K) :
    0 < tunedSlots K hK j := by
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  exact lt_of_lt_of_le (div_pos tuned_total_pos (by positivity))
    ((tunedSlots_spec K hK).2.2 j).1

theorem transport_tuned_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i=TunedCandidate.ell) (R : Set Id)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z‖≤C*Z^(TunedCandidate.signal TunedCandidate.B+loss) := by
  simpa only [tuned_low_power] using
    transport_original_ray_compensatedPhysicalProbe_low_loss
      TunedCandidate.ell TunedCandidate.lx TunedCandidate.ly tuned_total_pos.le tuned_total_le tuned_width_sum
      tuned_xy_lt tuned_source_growth S hS hmax ell hell hinj hsum.le R
      a b B loss ha hab hloss W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1
      ha0 ha1 hab1 hB0 hB1 hW0 hW1 hW0s hW1s hWB0 hWB1

theorem transport_tuned_low_gap
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i=TunedCandidate.ell) (R : Set Id)
    (a b B beta : ℝ) (ha : 0<a) (hab : a≤b) (hbeta : TunedCandidate.B<beta)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hB0 : 0≤B0) (hB1 : 0≤B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤B0) (hWB1 : ∀x,‖W1 x‖≤B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=>canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=>Z^(ell i))
        (Z^TunedCandidate.lx) (Z^TunedCandidate.ly) Z‖≤C*Z^(TunedCandidate.signal TunedCandidate.B+lowGap beta) := by
  exact transport_tuned_low_loss S hS hmax ell hell hinj hsum R a b B (lowGap beta)
    ha hab (lowGap_pos hbeta) W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1
    ha0 ha1 hab1 hB0 hB1 hW0 hW1 hW0s hW1s hWB0 hWB1

end
end LW56e2.Transport.PhysicalLow
