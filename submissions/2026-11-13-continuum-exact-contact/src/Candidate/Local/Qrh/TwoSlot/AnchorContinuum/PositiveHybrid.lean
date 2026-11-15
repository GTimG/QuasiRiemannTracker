/- Copyright (c) 2026 Joseph Bebel. Apache-2.0.
Variable-face Fourier restoration, including the native and empty-mark ranges.
Adapted from Sil's PR137 Hybrid adapter and predecessor work (Apache-2.0).
No fixed-fee physical schedule is assumed. -/
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveFourier
import Candidate.Local.Qrh.TwoSlot.AnchorContinuum.PositiveSource
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.JointDetector.BoundaryPhysical.PhysicalDirect.Hybrid

set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Qrh.TwoSlot.AnchorContinuum.PositiveTransport
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
open QRH.Record1252270103Return QRH.Record12518109Source
open Qrh.JointDetector.BoundaryPhysical.Return.GenericPhysical.PhysicalDirect
open OAI OAI.SevenEighths HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyBands CenteredMomentScaleSupremum
open CenteredMomentSectorLocalization CenteredMomentDetectorPlainFiberSource
open Cycle25WeightedNumeratorPhysical
variable {line : Qrh.TwoSlot.AnchorZeroLoss.Affine.Line}
variable [Geometry.Parameters]
variable [Qrh.TwoSlot.AnchorZeroLoss.Affine.Return.ImprovedCountScheme line]

/-- The explicit physical face and the genuine native cones cover every
restoration scale, including negative plain lengths and empty mark sets. -/
theorem hybrid_fourier_with_cost (A : ChosenData) {s : ℝ}
    (hs : 0 ≤ s) (hsmax : s ≤ 1/1000000000) (κ : ℝ)
    (hk0 : (7/10:ℝ) ≤ κ) (hk1 : κ ≤ (3/4:ℝ))
    (hb : (51/100:ℝ) ≤ HeckeZeroSupremum.beta) (hkb : 2*HeckeZeroSupremum.beta-1 ≤ κ)
    (bPhi error : ℝ) (herror : 0 < error)
    (hsPhi : Function.support (radialMajorant : ℝ → ℂ) ⊆ Set.Iic bPhi)
    (di : ℕ) (control : Finset (ℕ×ℕ)) (Ci : ℝ) (hCi : 0 < Ci)
    (hinput : ∀ᶠ U : ℝ in atTop,
      affineAtFace (PositiveSource.physicalFace s) A bPhi error U di control Ci) :
    ∃ degree J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      1 < U ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, U^(1/100:ℝ) ≤ rowNorm u ∧ rowNorm u ≤ U) →
      ∀ T : Finset (Fin A.D.N), ∀ width : T → ℝ, ∀ z : T → ℂ, ∀ height n : ℝ,
      (∀ i, 0 ≤ width i) → (∀ i, width i ≤ A.sourceMesh) →
      (∀ i, width i ≤ Cycle25.Energy.commonMesh 2 0 1 (A.D.t/4)) →
      (∀ i, (z i).re = 17/50) → 0 ≤ height → (∀ i, |(z i).im| ≤ height) →
      0 ≤ n → n ≤ 2 →
      ((2*n+(2+10*s)*(∑ i, width i) ≤ 1-s ∧ (∑ i, width i) ≤ 3/40) ∨
        (2*n+6*κ*(∑ i, width i) ≤ 1 ∨ T = ∅)) →
      ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ → X₁ ≤ U^n → X₂ ≤ U^n →
      length U X₁ ≤ n → length U X₂ ≤ n → ∀ j k : Fin 2, ∀ v w : ℝ,
      (∑ u ∈ rows, ‖polynomial (rowCharacter A.F.S A.F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) j) X₁ 0 (2*Real.pi*v) *
        polynomial (rowCharacter A.F.S A.F.exclusions.prime u).inverse false
        (scaleTest (fun y : ℝ => (annulus y : ℂ)) k) X₂ 0 (2*Real.pi*w) *
        ∏ i, HeckePrimeRow.canonicalPrimeAmplitude A.F.modulus ⊤ u.val A.F.W
          2 (U^(width i)) (z i)‖^2) ≤
      (C*(1+height)^degree*U^(1+A.D.t+error))*((1+‖v‖)^J)^2*((1+‖w‖)^J)^2 := by
  obtain ⟨Ja,Ca,hCa,ha⟩ := fourier_of_affine (PositiveSource.physicalFace s) A
    bPhi error hsPhi di control Ci hCi hinput
  obtain ⟨dp,Jp,Cp,hCp,hp⟩ := certified_reflected_fourier_moment A.F κ hk0 hk1 hb hkb
  obtain ⟨Jz,Cz,hCz,hz⟩ := certified_reflected_zero_fourier_moment A.F
  dsimp only [QRH.Record1252270103Return.GenericPhysical.BaselineData.toMomentData] at hp hz
  refine ⟨di+dp,Ja+Jp+Jz,Ca+Cp+Cz,by positivity,?_⟩
  filter_upwards [ha,hp,hz] with U ha hp hz
  have hU := ha.1
  have hUp := zero_lt_one.trans hU
  refine ⟨hU,?_⟩
  intro rows hrows T width z height n hw hmesh hwmax hzre hh him hn hn2 hcap
    X₁ X₂ hX₁ hX₂ hX₁max hX₂max hx₁ hx₂ j k v w
  have hsum : 0 ≤ ∑ i, width i := Finset.sum_nonneg (fun i _ => hw i)
  have ht := A.D.t_pos
  have hUerror : U^(1+error) ≤ U^(1+A.D.t+error) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [A.D.t_pos])
  have hUt : U^(1+A.D.t) ≤ U^(1+A.D.t+error) :=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith)
  have baseline (hbudget : 2*n+6*κ*(∑ i, width i) ≤ 1) := by
    have hn1 : n ≤ 1 := by nlinarith only [hbudget,hk0,hsum]
    have hpow : U^n ≤ U := by
      simpa using Real.rpow_le_rpow_of_exponent_le hU.le hn1
    exact hp.2 rows hrows T width z height hw hwmax hzre hh him X₁ X₂ hX₁ hX₂
      (hX₁max.trans hpow) (hX₂max.trans hpow)
      (by
        calc
          _ ≤ n+n+6*κ*(∑ i, width i) := add_le_add (add_le_add hx₁ hx₂) le_rfl
          _ = 2*n+6*κ*(∑ i, width i) := by ring
          _ ≤ 1 := hbudget) j k v w
  rcases hcap with hphysical | hold
  · have hnhalf : n ≤ (1/2:ℝ) := by
      have hm := mul_nonneg (show 0 ≤ 2+10*s by linarith) hsum
      linarith [hphysical.1]
    have hpow : U^n ≤ U := by
      simpa using Real.rpow_le_rpow_of_exponent_le hU.le (by linarith : n ≤ 1)
    by_cases h₁ : 0 ≤ length U X₁
    · by_cases h₂ : 0 ≤ length U X₂
      · have hadmit : (PositiveSource.physicalFace s).Admissible
          (length U X₁) (length U X₂) (∑ i, width i) 1 := by
          dsimp only [SourceFace.Admissible,PositiveSource.physicalFace]
          norm_num only [zero_mul,mul_one]
          exact ⟨h₁,by linarith,h₂,by linarith,hsum,hphysical.2,by linarith [hphysical.1]⟩
        have hbound := ha.2 rows hrows T width z height hw hmesh hzre hh him
          X₁ X₂ hX₁ hX₂ hadmit j k v w
        apply hbound.trans
        gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
      · have hc := PositiveSource.small_plain_shortening hs hsmax (le_of_not_ge h₂)
          hx₁ hphysical.1 hphysical.2
        have hbound := hp.2 rows hrows T width z height hw hwmax hzre hh him
          X₁ X₂ hX₁ hX₂ (hX₁max.trans hpow) (hX₂max.trans hpow)
          (by
            calc
              _ ≤ length U X₁+length U X₂+(9/2)*(∑ i, width i) :=
                add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith : 6*κ ≤ (9/2:ℝ)) hsum)
              _ ≤ 1 := by simpa only [add_comm] using hc) j k v w
        apply hbound.trans
        gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · have hc := PositiveSource.small_plain_shortening hs hsmax (le_of_not_ge h₁)
        hx₂ hphysical.1 hphysical.2
      have hbound := hp.2 rows hrows T width z height hw hwmax hzre hh him
        X₁ X₂ hX₁ hX₂ (hX₁max.trans hpow) (hX₂max.trans hpow)
        (by
          calc
            _ ≤ length U X₁+length U X₂+(9/2)*(∑ i, width i) :=
              add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith : 6*κ ≤ (9/2:ℝ)) hsum)
            _ ≤ 1 := hc) j k v w
      apply hbound.trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
  · rcases hold with hbudget | hempty
    · apply (baseline hbudget).trans
      gcongr <;> first | linarith [norm_nonneg v,norm_nonneg w]
    · subst T
      simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one]
      have hbound := hz.2 rows hrows X₁ X₂ hX₁ hX₂
        (hX₁max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2))
        (hX₂max.trans (Real.rpow_le_rpow_of_exponent_le hU.le hn2)) j k v w
      apply hbound.trans
      have hheight : 1 ≤ (1+height)^(di+dp) := one_le_pow₀ (by linarith)
      have hc : Cz ≤ (Ca+Cp+Cz)*(1+height)^(di+dp) := by nlinarith
      gcongr <;> first | exact hc | linarith [norm_nonneg v,norm_nonneg w]

end
end Qrh.TwoSlot.AnchorContinuum.PositiveTransport
#print axioms Qrh.TwoSlot.AnchorContinuum.PositiveTransport.hybrid_fourier_with_cost
