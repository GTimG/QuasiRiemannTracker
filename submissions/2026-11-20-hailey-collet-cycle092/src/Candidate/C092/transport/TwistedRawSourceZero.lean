/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
   Actual independently colored second zero, proved from the original tuple
   cap and the generic divisor zero theorem, rather than a common-η estimate. -/
import Candidate.C092.transport.TwistedRawSourceBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TwistedRawSource
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceRow
open QRH.SilDensitySplit.CubeFree.FP MixedOriginalNormCap MixedOriginalTail
local notation "Id" => Ideal HeckeFamily.O
local instance (priority := 2000) sumZeroDecEq {κ κ₂ : Type*} :
    DecidableEq (κ ⊕ κ₂) := Classical.decEq _

/-- The original root geometry caps every nonzero colored column, irrespective
    of ordinary colors. No comparison with an old cancelling aggregate occurs. -/
theorem sourceColumn_cap {ι : Type*} [Fintype ι] {a b : ℝ}
    (s : MixedPrincipalPair.Source ι a b) (ha : 0 < a)
    (ω₁ ω₂ : Id → ℂ) (seed I : Id) (hI : sourceColumn s ha ω₁ ω₂ seed I ≠ 0) :
    I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ sourceNormCap s.P b s.T s.d := by
  let V₁ := CenteredMomentLattice.normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁
  let V₂ := CenteredMomentLattice.normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂
  have hs₁ := (CenteredMomentTwist.normPowerProfile_support s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁).trans s.hs₁
  have hs₂ := (CenteredMomentTwist.normPowerProfile_support s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂).trans s.hs₂
  have hz : ∀ i, s.Wslot i 0 = 0 := by
    intro i
    by_contra hn
    have hh := (s.hW i hn).1
    norm_num at hh
  have hz₁ : V₁ 0 = 0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs₁ hn).1
  have hz₂ : V₂ 0 = 0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hs₂ hn).1
  have he : sourceColumn s ha ω₁ ω₂ seed I =
      finiteColumnCoefficient (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s))
        (fun v => (MixedCommonCoefficient.tupleWeight
          (MixedCommonRestriction.punctureProduct s.S s.H) v * ordinaryColor ω₁ ω₂ v) *
          profileCoefficient s.R s.ν s.Wslot s.P V₁ V₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.d.1 s.d.2 seed v) I := by
    unfold sourceColumn finiteColumnCoefficient
    apply Finset.sum_congr rfl
    intro v hv
    dsimp [MixedOriginalSecondZero.originalTuple, V₁, V₂]
    ring
  have hh := weighted_profile_column_norm
    (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s))
    (fun v => MixedCommonCoefficient.tupleWeight
      (MixedCommonRestriction.punctureProduct s.S s.H) v * ordinaryColor ω₁ ω₂ v)
    s.R seed s.ν s.Wslot s.P (fun _ => 2) V₁ V₂ b b s.X₁ s.X₂ s.Y₁ s.Y₂ s.d s.hd
    (fun i => zero_lt_one.trans_le (s.hP i)) (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) (s.hpX.trans s.hpY.symm)
    hz hz₁ hz₂ (fun i x hx => (s.hW i hx).2)
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2) I (he ▸ hI)
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  unfold sourceNormCap
  rw [s.hpX, Finset.prod_mul_distrib]
  ring

/-- Uniform divisor bound at the colored coefficient, with the same profile
    cap and slot count as the original source. -/
theorem sourceColumn_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {a b : ℝ}
      (s : MixedPrincipalPair.Source ι a b), Fintype.card ι ≤ N →
    ∀ (ha : 0 < a) (η₁ η₂ : Character) (seed I : Id) (Y : ℝ),
      I ≠ 0 → 1 ≤ Y → (Ideal.absNorm I : ℝ) ≤ Y →
      ‖sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I‖ ≤
        C * profileCap s * Y^ε := by
  let δ := ε / (N+2 : ℕ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδn : δ * (N+2 : ℕ) = ε := by dsimp [δ]; field_simp
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(1+D)^(N+2), by positivity, ?_⟩
  intro ι _ a b s hcard ha η₁ η₂ seed I Y hI hY hNI
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hb : 1 ≤ (1+D)*Y^δ := by
    have hy := Real.one_le_rpow hY hδ.le
    nlinarith
  have hdI : ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ) ≤ (1+D)*Y^δ := by
    apply (hd I hI).trans
    apply mul_le_mul (by linarith : D ≤ 1+D)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hNI hδ.le) (by positivity) (by positivity)
  have hc := finiteColumnCoefficient_norm_le
    (Fintype.piFinset (MixedPrincipalAllocations.tuplePools s))
    (fun v => MixedOriginalSecondZero.originalTuple s ha seed v *
      ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v)
    (profileCap s) (profileCap_nonneg s)
    (fun v _ _ => by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _)
        (ordinaryColor_norm_le_one η₁ η₂ v)).trans
        (MixedOriginalSecondZero.original_tuple_norm s ha seed v)) I hI
  calc
    _ ≤ profileCap s * ((IdealMobiusDivisorSum.idealDivisors I).card : ℝ)^(Fintype.card ι+2) := hc
    _ ≤ profileCap s * ((1+D)*Y^δ)^(Fintype.card ι+2) := by
      have hp := profileCap_nonneg s
      gcongr
    _ ≤ profileCap s * ((1+D)*Y^δ)^(N+2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb (by omega)) (profileCap_nonneg s)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hY0.le, hδn]
      ring

/-- Genuine colored second zero, including the original reciprocal seed norm.
    This theorem has no source-energy or child-estimate premise. -/
theorem source_second_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {a b : ℝ}
      (s : MixedPrincipalPair.Source ι a b), Fintype.card ι ≤ N →
    ∀ (ha : 0 < a) (η₁ η₂ : Character) (seed : Id), seed ≠ 0 →
    ∀ (τ : Character) (t Y : ℝ), 1 ≤ Y → sourceNormCap s.P b s.T s.d ≤ Y →
      ‖CenteredMomentSourceSecondZeroEnergy.sourceSecondZero (MixedPrincipalWindow.sourceColumns s)
        (sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed) τ t‖ ≤
        C * profileCap s^2 * Y^(1+ε) / (Ideal.absNorm seed : ℝ) := by
  obtain ⟨C₀, hC₀, hc⟩ := sourceColumn_bound N (ε/2) (half_pos hε)
  refine ⟨128*C₀^2, by positivity, ?_⟩
  intro ι _ a b s hN ha η₁ η₂ seed hseed τ t Y hY hcap
  have hsize : ∀ I ∈ supportedColumns (MixedPrincipalWindow.sourceColumns s),
      sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I ≠ 0 →
      (Ideal.absNorm I : ℝ) ≤ Y := fun I _ hi =>
    (sourceColumn_cap s ha _ _ seed I hi).2.trans hcap
  have hh := CenteredMomentSourceSecondZeroEnergy.sourceSecondZero_divisor_bound
    (MixedPrincipalWindow.sourceColumns s) (sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed)
    τ t (C₀*profileCap s*Y^(ε/2)) Y
    (by have hp := profileCap_nonneg s; positivity) (by linarith) seed hseed
    (fun I hI hi => hc s hN ha η₁ η₂ seed I Y
      (sourceColumn_cap s ha _ _ seed I hi).1 hY (hsize I hI hi))
    (fun I _ hi => by
      by_contra hn
      exact hi (by rw [sourceColumn_seed, ite_eq_right hn])) hsize
  have hp : (Y^(ε/2))^2 * Y = Y^(1+ε) := by
    rw [← Real.rpow_mul_natCast (zero_lt_one.trans_le hY).le]
    norm_num only [Nat.cast_ofNat]
    rw [show ε/2*(2:ℝ) = ε by ring]
    calc
      _ = Y^ε * Y^(1:ℝ) := by rw [Real.rpow_one]
      _ = Y^(ε+1) := (Real.rpow_add (zero_lt_one.trans_le hY) _ _).symm
      _ = _ := by congr 1; ring
  exact hh.trans_eq (by rw [show 128*(C₀*profileCap s*Y^(ε/2))^2*Y =
    128*C₀^2*profileCap s^2*((Y^(ε/2))^2*Y) by ring, hp])

#print axioms sourceColumn_cap
#print axioms sourceColumn_bound
#print axioms source_second_zero
end
end QRH.Cycle092.TwistedRawSource
