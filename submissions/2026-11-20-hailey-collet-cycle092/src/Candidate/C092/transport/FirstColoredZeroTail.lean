/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
First-Poisson zero and tail for the literal independently colored source.
Normalization and tail-order arithmetic reuse Sil's credited native lemmas;
the analytic kernels below are applied to the actual colored coefficients. -/
import Candidate.C092.transport.TwistedRawSourceTail
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstRemainder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.FirstColoredZeroTail
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentFirstLocalization
open CenteredMomentSourceInputFirstSectorTail CenteredMomentSectorLocalization
open CenteredMomentSourceInputTailUniform (eventually_tail_threshold)
open EisensteinSchwartzPoisson QRH.Record1252270103KernelMass
open QRH.SilDensitySplit.CubeFree.FP
open MixedFirstLiveRemainders
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow
open MixedOriginalNormCap MixedOriginalTail MixedOriginalSecondZero MixedInnerExceptionalBlock
open CenteredMomentSourceProfileMass
open MixedFirstRemainder (first_zero_normalization source_cap_volume supportHeight choose_first_tail_order)
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance (priority := 2000) coloredZeroDecEq {κ κ₂ : Type*} : DecidableEq (κ ⊕ κ₂) := Classical.decEq _

/-- The native arbitrary-tuple first-zero kernel reads the colored literal
coefficients themselves. Changing ordinary phases never invokes a comparison
with the differently cancelling uncolored aggregate. -/
theorem actual_first_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (ι : Type u) [Fintype ι],∀ a b : ℝ,∀ s : Source ι a b,
    Fintype.card ι ≤ N → ∀ ha : 0 < a,∀ (η₁ η₂ : Character) (seed : Id)
    (η : Character) (m A : O) (t K Y : ℝ) (Φ : 𝓢(ℝ,ℂ)),
    0 ≤ K → 1 ≤ Y → sourceNormCap s.P b s.T s.d ≤ Y →
    ‖zeroEnergy η m A t (sourceColumns s)
      (TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed) Φ K‖ ≤
      C*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*Y^(1+ε) := by
  obtain ⟨C,hC,hzero⟩ := active_tuple_zero_energy_bound N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ a b s hcard ha η₁ η₂ seed η m A t K Y Φ hK hY hcap
  let β := fun v=>originalTuple s ha seed v * TwistedRawSource.ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v
  have hβ (v) (_ : v∈Fintype.piFinset (tuplePools s)) (_ : finiteTupleProduct v≠0) :
      ‖β v‖ ≤ profileCap s := by
    rw [show β v=originalTuple s ha seed v * TwistedRawSource.ordinaryColor (idealCoeff η₁) (idealCoeff η₂) v from rfl,norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (TwistedRawSource.ordinaryColor_norm_le_one η₁ η₂ v)).trans (original_tuple_norm s ha seed v)
  have hh := hzero hcard η m A t (Fintype.piFinset (tuplePools s)) β Φ Y K
    (profileCap s) hY hK (profileCap_nonneg s) hβ (fun I _ hi=>
      (TwistedRawSource.sourceColumn_cap s ha _ _ seed I hi).2.trans hcap)
  exact hh

private theorem source_cap_nonneg {ι : Type u} [Fintype ι] {a b : ℝ} (s : Source ι a b) :
    0 ≤ sourceNormCap s.P b s.T s.d := by
  have he : sourceNormCap s.P b s.T s.d=b^2*(2:ℝ)^Fintype.card ι*sourceVolume s/pairNorm s.d := by
    rw [source_cap_factored]
    unfold sourceVolume
    rw [←s.hpX]
    ring
  rw [he]
  exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg b) (pow_nonneg (by norm_num) _))
    (sourceVolume_pos s).le) (pairNorm_pos s.hd.1 s.hd.2).le

/-- Original first-zero prefix normalization; subunit support vanishes using
actual colored support, rather than replacing its support radius by max(1,Y). -/
theorem normalized_first_zero (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (ι : Type u) [Fintype ι],∀ a b : ℝ,∀ s : Source ι a b,
    Fintype.card ι ≤ N → ∀ ha : 0 < a,0 < b → ∀ (η₁ η₂ : Character) (seed : Id)
    (η : Character) (m A : O) (t K : ℝ) (Φ : 𝓢(ℝ,ℂ)),0 ≤ K →
    ‖zeroEnergy η m A t (sourceColumns s)
      (TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed) Φ K‖/sourceVolume s ≤
      C*K*(profileCap s)^2*‖paperRadialFourier Φ 0‖*
        (b^2*(2:ℝ)^Fintype.card ι/pairNorm s.d)*(sourceNormCap s.P b s.T s.d)^ε := by
  obtain ⟨C,hC,hzero⟩ := actual_first_zero N ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ a b s hcard ha hb η₁ η₂ seed η m A t K Φ hK
  have hv := sourceVolume_pos s
  have hp := pairNorm_pos s.hd.1 s.hd.2
  by_cases hy : 1 ≤ sourceNormCap s.P b s.T s.d
  · have hh := div_le_div_of_nonneg_right
      (hzero ι a b s hcard ha η₁ η₂ seed η m A t K _ Φ hK hy le_rfl) hv.le
    apply hh.trans_eq
    rw [mul_div_assoc,first_zero_normalization s hb ε]
    ring
  · have hz (I : Id) : TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I=0 := by
      by_contra hi
      have hh := TwistedRawSource.sourceColumn_cap s ha _ _ seed I hi
      exact hy ((ideal_norm_one_le hh.1).trans hh.2)
    simp only [zeroEnergy,hz,zero_mul,mul_zero,Finset.sum_const_zero,norm_zero,zero_div]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hK) (sq_nonneg _)) (norm_nonneg _))
        (div_nonneg (mul_nonneg (sq_nonneg b) (pow_nonneg (by norm_num) _)) hp.le))
      (Real.rpow_nonneg (source_cap_nonneg s) _)

/-- The arbitrary-coefficient FIRST discarded kernel uses the colored cap
and colored coefficient mass. No second-Poisson density or K4 replacement. -/
theorem actual_first_discarded (Adec N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (control : Finset (ℕ×ℕ)) (C : ℝ),0 < C ∧
    ∀ (ι : Type u) [Fintype ι],∀ a b : ℝ,∀ s : Source ι a b,
    Fintype.card ι ≤ N → ∀ ha : 0 < a,0 ≤ b → ∀ (η₁ η₂ : Character) (seed : Id)
    (η : Character) (m A : O) (t K Tsec Z ξ : ℝ) (Φ : 𝓢(ℝ,ℂ)),0 < K → 1 < Z →
    (sourceVolume s)^2/K ≤ Tsec →
    2*supportHeight N b/Real.log Z+Real.log (4:ℝ)/Real.log Z < ξ/4 →
    ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t
      (sourceColumns s) (TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed)
      Φ K (sourceVolume s) Z ξ‖ ≤
      (massCap s)^2*(Real.exp (supportHeight N b)*sourceVolume s)^ε*K*
        (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
        ((min 1 (kernelReference Tsec (supportHeight N b)))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨control,C,hC,htail⟩ := local_discarded_energy_bound Adec ε hε
  refine ⟨control,C,hC,?_⟩
  intro ι _ a b s hN ha hb η₁ η₂ seed η m A t K Tsec Z ξ Φ hK hZ hscale hthreshold
  have ht := htail η m A t (sourceColumns s)
    (TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed) Φ K
    (sourceVolume s) (supportHeight N b) Tsec Z 1 ξ hK (sourceVolume_pos s) hZ le_rfl
    (fun I _ hi=>(TwistedRawSource.sourceColumn_cap s ha _ _ seed I hi).2.trans (source_cap_volume s N hN)) hscale
    (by simpa only [mul_one] using hthreshold)
  let factor := (Real.exp (supportHeight N b)*sourceVolume s)^ε*K*
    (C*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)/
      ((min 1 (kernelReference Tsec (supportHeight N b)))^2*(1+Z^(ξ/4))^Adec)
  have hf : 0 ≤ factor := by
    have := (sourceVolume_pos s).le
    have := (show 0 ≤ control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ from apply_nonneg _ _)
    dsimp only [factor]
    positivity
  have hm := pow_le_pow_left₀
    (Finset.sum_nonneg (fun I _=>norm_nonneg (TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I)))
    (TwistedRawSource.sourceColumn_mass s ha hb η₁ η₂ seed) 2
  apply ht.trans
  calc
    _=(∑I∈sourceColumns s,‖TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed I‖)^2*factor := by dsimp only [factor];ring
    _ ≤ (massCap s)^2*factor := mul_le_mul_of_nonneg_right hm hf
    _=_ := by dsimp only [factor];ring

/-- Arbitrary saving after exactly one original source-volume normalization.
All radius, volume and all-column pool caps remain explicit. -/
theorem normalized_first_tail (N : ℕ) (b B ξ saving : ℝ) (hB : 0 ≤ B) (hξ : 0 < ξ) :
    ∃ (control : Finset (ℕ×ℕ)) (C : ℝ),0 < C ∧ ∀ᶠ Z : ℝ in atTop,1 < Z ∧
    ∀ (ι : Type u) [Fintype ι],∀ a : ℝ,∀ s : Source ι a b,Fintype.card ι ≤ N →
    ∀ ha : 0 < a,0 ≤ b → ∀ (η₁ η₂ : Character) (seed : Id) (η : Character) (m A : O)
    (t K : ℝ) (Φ : 𝓢(ℝ,ℂ)),0 < K → poolCap s ≤ Z^B → sourceVolume s ≤ Z^B → K ≤ Z^B → K⁻¹ ≤ Z^B →
    ‖CenteredMomentFirstSectorLocalization.discardedEnergy η m A t
      (sourceColumns s) (TwistedRawSource.sourceColumn s ha (idealCoeff η₁) (idealCoeff η₂) seed)
      Φ K (sourceVolume s) Z ξ‖/sourceVolume s ≤
      C*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨Adec,horder⟩ := choose_first_tail_order B ξ saving hB hξ
  obtain ⟨control,C0,hC0,htail⟩ := actual_first_discarded Adec N 1 (by norm_num)
  let H := supportHeight N b
  refine ⟨control,C0*Real.exp H*(1+Real.exp (2*H))^2,by positivity,?_⟩
  filter_upwards [eventually_tail_threshold H ξ hξ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ a s hN ha hb η₁ η₂ seed η m A t K Φ hK hpool hV hKcap hKinv
  have hz := zero_lt_one.trans hZ.1
  have hv := sourceVolume_pos s
  have hscale : (sourceVolume s)^2/K ≤ Z^(3*B) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hv.le hV 2) hKinv
      (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  have ht := htail ι a b s hN ha hb η₁ η₂ seed η m A t K (Z^(3*B)) Z ξ Φ
    hK hZ.1 hscale hZ.2
  have hn := horder Z H (poolCap s) K hZ.1.le (poolCap_nonneg s) hK hpool hKcap
  have hc : 0 ≤ control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ := apply_nonneg _ _
  apply (div_le_div_of_nonneg_right ht hv.le).trans
  calc
    _=(C0*Real.exp H*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        ((poolCap s)^2*K*((min 1 (kernelReference (Z^(3*B)) H))^2)⁻¹*
          ((1+Z^(ξ/4))^Adec)⁻¹) := by
      let R := (C0*Real.exp H*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        ((poolCap s)^2*K*((min 1 (kernelReference (Z^(3*B)) H))^2)⁻¹*
          ((1+Z^(ξ/4))^Adec)⁻¹)
      change _=R
      calc
        _=R*(sourceVolume s*(sourceVolume s)⁻¹) := by
          dsimp only [R,H]
          simp only [Real.rpow_one,massCap,div_eq_mul_inv,mul_inv_rev,mul_pow]
          ring
        _=R := by rw [mul_inv_cancel₀ hv.ne',mul_one]
    _ ≤ (C0*Real.exp H*(profileCap s)^2*control.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ)*
        ((1+Real.exp (2*H))^2*Z^(-saving)) := mul_le_mul_of_nonneg_left hn (by positivity)
    _=_ := by ring

#print axioms actual_first_zero
#print axioms normalized_first_zero
#print axioms actual_first_discarded
#print axioms normalized_first_tail
end
end QRH.Cycle092.FirstColoredZeroTail
