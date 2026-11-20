/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Unnormalized fixed-row H.15 retains both original profile heights. -/
import Candidate.C092.transport.FixedFourierH15Window

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve RayFourExpansion FourierBridge
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentSmooth
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentDivisorAllocation
open CenteredMomentRowNorm CenteredMomentSecondSectorColumns CenteredMomentChildRows CenteredMomentChildAssembly
open QRH.SilDensitySplit.CubeFree.FP MixedPrincipalPair MixedCommonHeights
open QRH.Cycle092.SignedCenter
open MixedPrincipalWindow MixedCommonRestriction
open QRH.Cycle092.FixedCubeGauss
namespace QRH.Cycle092.FixedFourierH15
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type*} [Fintype ι] {a b : ℝ}

def sourceVolume (r : Source ι a b) : ℝ := r.T*∏ i:ι,r.P i

def sourcePrefix (r : Source ι a b) (G L : Id) : ℝ :=
  ((r.d.1.absNorm:ℝ)*r.d.2.absNorm)*G.absNorm*L.absNorm

def profileHeightCost (r : Source ι a b) (t θ : ℝ) (J : ℕ) : ℝ :=
  (2*(1+‖r.t₁‖+‖r.t₂‖))^(2*J)*heightCost t θ^(2*J)

lemma sourceVolume_pos (r : Source ι a b) : 0 < sourceVolume r := by
  unfold sourceVolume
  exact mul_pos r.total_pos (Finset.prod_pos (fun i _=>zero_lt_one.trans_le (r.hP i)))

lemma sourcePrefix_pos (r : Source ι a b) (G L : Id) (hG : G≠0) (hL : L≠0) :
    0 < sourcePrefix r G L := by
  have hn (I:Id) (h:I≠0) : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h)
  exact mul_pos (mul_pos (mul_pos (hn _ r.hd.1) (hn _ r.hd.2)) (hn _ hG)) (hn _ hL)

lemma shifted_profile_height (t₁ t₂ v : ℝ) :
    1+‖t₁+v‖+‖t₂+v‖ ≤ (2*(1+‖t₁‖+‖t₂‖))*(1+‖v‖) := by
  have h1 := norm_add_le t₁ v
  have h2 := norm_add_le t₂ v
  have h0 : 0 ≤ (‖t₁‖+‖t₂‖)*‖v‖ := mul_nonneg (by positivity) (norm_nonneg _)
  nlinarith [norm_nonneg t₁,norm_nonneg t₂,norm_nonneg v]

/-- Normalization is removed exactly once, leaving the original physical
volume. This remains a pointwise statement on the actual native fixed row. -/
theorem colored_window_unnormalized (r : Source ι a b) (ha : 0<a) (hb : 0 ≤ b)
    (D : FixedCubeDatum) (ω₁ ω₂ η : Character) (χ : RayCharacter)
    (hη : D.η=childCharacter η χ) (hm : D.m=nativeSourceMask r)
    (G : Id) (hG : Supported G) (L : Id) (hL : Squarefree L)
    (t θ X : ℝ) (hX : 0<X) (V : ℝ→ℂ) (hc : HasCompactSupport V) (hs : ContDiff ℝ ∞ V)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hheight : ∀ v : ℝ,‖coloredFullyAllocatedPhysicalHeight r ha hb D ω₁ ω₂ G L v‖^2 ≤
      E*(1+‖r.t₁+v‖+‖r.t₂+v‖)^(2*J)) :
    ‖nativeWindowPolynomial r ha D ω₁ ω₂ η χ G hG L t θ X V‖^2 ≤
      E*sourceVolume r*profileHeightCost r t θ J*(windowMass V hc hs J)^2 := by
  have hbnd := colored_window_square r ha hb D ω₁ ω₂ η χ hη hm G hG L hL t θ X hX V hc hs J
    (E*(2*(1+‖r.t₁‖+‖r.t₂‖))^(2*J)) (by positivity) ?_
  · have hN : ‖MixedLiveNormalization.normalization (r.X₁*r.X₂) r.P‖^2=(sourceVolume r)⁻¹ := by
      rw [r.hpX]
      simpa [sourceVolume,mul_inv_rev] using
        MixedLiveNormalization.normalization_sq r.T r.total_pos r.P
          (fun i=>zero_lt_one.trans_le (r.hP i))
    rw [norm_mul,mul_pow,hN] at hbnd
    have hv := sourceVolume_pos r
    have hh := mul_le_mul_of_nonneg_left hbnd hv.le
    have heq : sourceVolume r*((sourceVolume r)⁻¹*
        ‖nativeWindowPolynomial r ha D ω₁ ω₂ η χ G hG L t θ X V‖^2)=
        ‖nativeWindowPolynomial r ha D ω₁ ω₂ η χ G hG L t θ X V‖^2 := by
      field_simp
    rw [heq] at hh
    convert hh using 1 <;> unfold profileHeightCost <;> ring
  · intro v
    apply (hheight v).trans
    calc
      _ ≤ E*((2*(1+‖r.t₁‖+‖r.t₂‖))*(1+‖v‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (shifted_profile_height r.t₁ r.t₂ v) _) hE
      _ = _ := by rw [mul_pow];ring

#print axioms colored_window_unnormalized
end QRH.Cycle092.FixedFourierH15
