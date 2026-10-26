/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CoupledFirstRemainder

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Low
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CenteredMomentHeckeExpansion
open CenteredMomentSourceMass CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentPositiveSummability CenteredMomentAbsoluteEnergy CenteredMomentPlainEnergy
open CenteredMomentAddedZeroUniform CenteredMomentCommonRadialData
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentSourceInputTailUniform CenteredMomentExceptionalAmplitudePair
open QRH.Record1252270103Source.High.CoupledFirst
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def firstNormalizedRow (s : Input ι) (modifier : Tuple ι→ℂ) (R : Ideal O) (A z : O) : ℂ :=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    ∑I∈finiteColumns (Fintype.piFinset s.pools),coefficient s modifier R 1 I*
      rowWeight s.η (fixedBadMask*idealGenerator R) A z s.t I

/-- Finite kept rows are bounded by the complete positive norm of the SAME
literal modified coefficient. Only the row predicate is enlarged. -/
theorem finite_first_normalized_le_full (s : Input ι) (modifier : Tuple ι→ℂ)
    (R : Ideal O) (A : O) (rows : Finset O) (keep : O→Prop)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (hΦ : ∀x,0≤(Φ x).re) :
    (∑z∈rows,if keep z then ‖firstNormalizedRow s modifier R A z‖^2*
      (Φ (‖eisEmbedding z‖^2/K)).re else 0)≤
      ‖finiteHeckeEnergy s.η (fixedBadMask*idealGenerator R) A s.t
        (finiteColumns (Fintype.piFinset s.pools)) (coefficient s modifier R 1) Φ K‖/volume s.toData := by
  let S:=finiteColumns (Fintype.piFinset s.pools)
  let β:=coefficient s modifier R 1
  let f:=fun z : O=>∑I∈S,β I*rowWeight s.η (fixedBadMask*idealGenerator R) A z s.t I
  let E:=finiteHeckeEnergy s.η (fixedBadMask*idealGenerator R) A s.t S β Φ K
  have hml : goodLambda∣fixedBadMask*idealGenerator R :=
    (dvd_mul_right goodLambda 2).trans (dvd_mul_right _ _)
  have hm2 : (2:O)∣fixedBadMask*idealGenerator R :=
    (dvd_mul_left 2 goodLambda).trans (dvd_mul_right _ _)
  have hs : Summable (fun z : O=>((‖f z‖^2:ℝ):ℂ)*Φ (‖eisEmbedding z‖^2/K)) := by
    dsimp only [f]
    simp_rw [finite_hecke_sum_eq_rowPolynomial s.η (fixedBadMask*idealGenerator R) A _ s.t hml hm2]
    exact rowEnergy_summable Finset.univ (sourceGenerator S) (sourceGenerator_supported S) _ Φ K hK
  have hr : HasSum (fun z : O=>‖f z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re) E.re := by
    have hh:=Complex.hasSum_re hs.hasSum
    simpa only [E,finiteHeckeEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero] using hh
  have hnorm (z : O) : ‖firstNormalizedRow s modifier R A z‖^2=‖f z‖^2/volume s.toData :=
    CenteredMomentDivisorRawEnergy.normalized_norm_sq (volume s.toData) (volume_pos s) (f z)
  have hfinite := (hr.summable.div_const (volume s.toData)).sum_le_tsum rows
    (fun z _=>div_nonneg (mul_nonneg (sq_nonneg _) (hΦ _)) (volume_pos s).le)
  rw [tsum_div_const,hr.tsum_eq] at hfinite
  apply (Finset.sum_le_sum (fun z _=>?_)).trans
    (hfinite.trans (div_le_div_of_nonneg_right (Complex.re_le_norm E) (volume_pos s).le))
  by_cases hz : keep z
  · simp only [hz,ite_true,hnorm,div_mul_eq_mul_div,le_refl]
  · simp only [hz,ite_false]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (hΦ _)) (volume_pos s).le

/-- The existing physical reduction applies to every actually bounded tuple
modifier, including the literal marked/ordinary squarefree projector. -/
theorem finite_first_physical_reduction (hi : ι→ℝ) (wlo whi B ε ξ saving : ℝ)
    (hhi : ∀i,0≤hi i) (hwlo : 0<wlo) (hwhi : 0≤whi) (hB : 0≤B)
    (hε : 0<ε) (hξ : 0<ξ) :
    ∃Sdiag Stail : Finset (ℕ×ℕ),∃Cdiag Ctail : ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ : ℝ in Filter.atTop,1<Z ∧ ∀(s : Input ι)(modifier : Tuple ι→ℂ)(W₁ W₂ : 𝓢(ℝ,ℂ)),
      (∀v∈Fintype.piFinset s.pools,‖modifier v‖≤1) →
      s.W₁=W₁ →s.W₂=W₂ →Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi →(∀i,s.hi i≤hi i) →
      ∀(R : Ideal O)(A : O)(rows : Finset O)(keep : O→Prop)(Φ : 𝓢(ℝ,ℂ))(K : ℝ),
      0<K →(∀x,0≤(Φ x).re) →volume s.toData≤Z^B →K⁻¹≤Z^B →
      (∑z∈rows,if keep z then ‖firstNormalizedRow s modifier R A z‖^2*
        (Φ (‖eisEmbedding z‖^2/K)).re else 0)≤
      physicalMass s modifier R 1 (fixedBadMask*idealGenerator R) A Φ K Z ξ/volume s.toData+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,h⟩ := original_first_physical_reduction hi wlo whi B ε ξ saving
    hhi hwlo hwhi hB hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s modifier W₁ W₂ hmod he₁ he₂ hs₁ hs₂ hshi R A rows keep Φ K hK hΦ hV hKi
  have hh:=hZ.2 s modifier 1 W₁ W₂ zero_le_one
    (fun v hv=>hmod v (by simpa only [Fintype.mem_piFinset] using hv)) he₁ he₂ hs₁ hs₂ hshi
    (fixedBadMask*idealGenerator R) A ((dvd_mul_right goodLambda 2).trans (dvd_mul_right _ _))
    ((dvd_mul_left (2:O) goodLambda).trans (dvd_mul_right _ _)) R 1 Φ K hK hV hKi
  simp only [one_mul] at hh
  exact (finite_first_normalized_le_full s modifier R A rows keep Φ K hK hΦ).trans hh

end
end QRH.Record1252270103Low
#print axioms QRH.Record1252270103Low.finite_first_normalized_le_full
#print axioms QRH.Record1252270103Low.finite_first_physical_reduction
