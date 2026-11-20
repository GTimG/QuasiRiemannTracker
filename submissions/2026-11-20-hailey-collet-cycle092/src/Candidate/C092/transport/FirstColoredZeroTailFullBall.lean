/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Actual full-ball first remainders for independently colored root columns.
The B=8 radius arithmetic follows Sil's native remainder proof; its analytic
estimates are replaced by the checked colored arbitrary-coefficient kernels. -/
import Candidate.C092.transport.FirstColoredZeroTail
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FirstColoredZeroTail
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentHeckeExpansion
open CenteredMomentFirstLocalization CenteredMomentSourceProfileMass
open EisensteinSchwartzPoisson QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedFirstLiveRemainders
open MixedPrincipalPair MixedPrincipalWindow MixedOriginalNormCap MixedOriginalTail MixedInnerExceptionalBlock
local notation "O" => HeckeFamily.O

/-- Uniform in both ordinary colors and the outer character/mask/height.
Only authentic unit-root polynomial metadata and the original profile budget
are inputs. The colored first zero and discarded term are proved inside. -/
theorem uniform_unit_zero_tail (N : ℕ) (Ψ : 𝓢(ℝ,ℂ)) (cRad Cp ε ξ : ℝ)
    (hcRad : 1 ≤ cRad) (hCp : 0 < Cp) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ (ι : Type u) [Fintype ι],∀ s : Source ι (1/4) (9/4),
    Fintype.card ι ≤ N → s.d=(1,1) → ∀ B : ℝ,0 ≤ B →
    (profileCap s)^2 ≤ Cp*B → poolCap s ≤ Z^(8:ℝ) →
    sourceNormCap s.P (9/4) s.T s.d ≤ Z^(8:ℝ) → sourceVolume s ≤ Z^(8:ℝ) →
    ∀ (η₁ η₂ η : Character) (m A : O) (tp : ℝ),
    ‖zeroEnergy η m A tp (sourceColumns s)
      (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1) Ψ (cRad*Z)‖/sourceVolume s+
    ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s)
      (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)
      Ψ (cRad*Z) (sourceVolume s) Z ξ‖/sourceVolume s ≤ C*B*Z^(1+ε) := by
  obtain ⟨Cz,hCz,hzero⟩ := normalized_first_zero N (ε/16) (by positivity)
  obtain ⟨control,Ct,hCt,htail⟩ := normalized_first_tail N (9/4) 8 ξ 1 (by norm_num) hξ
  let F0 := ‖paperRadialFourier Ψ 0‖
  let Ft := control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ
  have hF0 : 0 ≤ F0 := norm_nonneg _
  have hFt : 0 ≤ Ft := apply_nonneg _ _
  let Cz' := Cz*cRad*Cp*(1+F0)*((9/4:ℝ)^2*(2:ℝ)^N)
  let Ct' := Ct*Cp*(1+Ft)
  have hcr : 0 < cRad := zero_lt_one.trans_le hcRad
  have hCz' : 0 < Cz' := by dsimp only [Cz'];positivity
  have hCt' : 0 < Ct' := by dsimp only [Ct'];positivity
  refine ⟨Cz'+Ct',add_pos hCz' hCt',?_⟩
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_ge_atTop cRad,htail] with Z hZ2 hcZ ht
  have hZ : 1 < Z := by linarith
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hK : 0 < cRad*Z := mul_pos hcr hz
  have hKcap : cRad*Z ≤ Z^(8:ℝ) := by
    calc
      _ ≤ Z*Z := mul_le_mul_of_nonneg_right hcZ hz.le
      _=Z^(2:ℝ) := by rw [Real.rpow_two];ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ.le (by norm_num)
  have hKinv : (cRad*Z)⁻¹ ≤ Z^(8:ℝ) :=
    (inv_le_one_of_one_le₀ (one_le_mul_of_one_le_of_one_le hcRad hZ.le)).trans
      (Real.one_le_rpow hZ.le (by norm_num))
  refine ⟨hZ,?_⟩
  intro ι _ s hn hunit B hB hprofile hpool hnorm hvol η₁ η₂ η m A tp
  have hnorm0 : 0 ≤ sourceNormCap s.P (9/4) s.T s.d := by
    rw [source_cap_factored]
    have hp : 0 ≤ ∏i,s.P i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))
    have hT := s.total_pos
    have hd : 0 < pairNorm s.d := pairNorm_pos s.hd.1 s.hd.2
    positivity
  have hnormpow : (sourceNormCap s.P (9/4) s.T s.d)^(ε/16) ≤ Z^(ε/2) := by
    apply (Real.rpow_le_rpow hnorm0 hnorm (by positivity : 0 ≤ ε/16)).trans_eq
    rw [←Real.rpow_mul hz.le]
    congr 1
    ring
  have hprefix : (9/4:ℝ)^2*(2:ℝ)^Fintype.card ι/pairNorm s.d ≤ (9/4:ℝ)^2*(2:ℝ)^N := by
    rw [hunit]
    simpa only [pairNorm,map_one,Nat.cast_one,mul_one,div_one] using
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn) (sq_nonneg (9/4:ℝ))
  have hprefix0 : 0 ≤ (9/4:ℝ)^2*(2:ℝ)^Fintype.card ι/pairNorm s.d :=
    div_nonneg (by positivity) (pairNorm_pos s.hd.1 s.hd.2).le
  have hz0 := hzero ι (1/4) (9/4) s hn (by norm_num) (by norm_num) η₁ η₂ 1 η m A tp (cRad*Z) Ψ hK.le
  have ht0 := ht.2 ι (1/4) s hn (by norm_num) (by norm_num) η₁ η₂ 1 η m A tp (cRad*Z) Ψ
    hK hpool hvol hKcap hKinv
  have hzpaid : ‖zeroEnergy η m A tp (sourceColumns s)
      (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1) Ψ (cRad*Z)‖/sourceVolume s ≤
      Cz'*B*Z^(1+ε) := by
    apply hz0.trans
    calc
      _ ≤ Cz*(cRad*Z)*(Cp*B)*(1+F0)*((9/4:ℝ)^2*(2:ℝ)^N)*Z^(ε/2) := by
        gcongr <;> (dsimp only [F0];linarith)
      _=Cz'*B*Z^(1+ε/2) := by
        rw [Real.rpow_add hz,Real.rpow_one]
        dsimp only [Cz']
        ring
      _ ≤ _ := by gcongr <;> linarith
  have htpaid : ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A tp (sourceColumns s)
      (TwistedRawSource.sourceColumn s (by norm_num) (idealCoeff η₁) (idealCoeff η₂) 1)
      Ψ (cRad*Z) (sourceVolume s) Z ξ‖/sourceVolume s ≤ Ct'*B*Z^(1+ε) := by
    apply ht0.trans
    calc
      _ ≤ Ct*(Cp*B)*(1+Ft)*Z^(-(1:ℝ)) := by
        gcongr <;> (dsimp only [Ft];linarith)
      _=Ct'*B*Z^(-(1:ℝ)) := by dsimp only [Ct'];ring
      _ ≤ _ := by gcongr <;> linarith
  exact (add_le_add hzpaid htpaid).trans_eq (by ring)

#print axioms uniform_unit_zero_tail
end
end QRH.Cycle092.FirstColoredZeroTail
