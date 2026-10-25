/- Copyright (c) 2026 Sil. Apache-2.0.
Actual source support bounds, including the original prefix norms.
The bounds concern full ideal norms, including prime powers. No radical
bound is substituted for a bound on the original source.
-/
import Candidate.SilPrior.FourthPower.MixedHeightEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceZeroEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.SilPrior.FourthPower.MixedOriginalNormCap
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSupportedZeroEnergy CenteredMomentSourceZeroEnergy
open MixedHeightEnergy MixedLiteralAllocation MixedCommonRestriction MixedCommonCoefficient
open MixedCanonicalSource MixedFrozenSource ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {α : Type*} [Fintype α]
local instance {β : Type*} : DecidableEq (β⊕Fin 2) := Classical.decEq _

/-- An arbitrary literal multiplier can reduce support, but cannot add
new column norms. The original profile bound therefore survives it. -/
theorem weighted_profile_column_norm (Q : Finset (Tuple α)) (weight : Tuple α→ℂ)
    (R seed : Id) (ν : α→Id→ℂ) (Wslot : α→ℝ→ℂ) (P upper : α→ℝ)
    (W₁ W₂ : ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0)
    (hP : ∀i,0<P i) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (hz : ∀i,Wslot i 0=0) (hz₁ : W₁ 0=0) (hz₂ : W₂ 0=0)
    (hs : ∀i x,Wslot i x≠0→x≤upper i)
    (hs₁ : ∀x,W₁ x≠0→x≤b₁) (hs₂ : ∀x,W₂ x≠0→x≤b₂)
    (I : Id) (hI : finiteColumnCoefficient Q (fun u=>weight u*
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ d.1 d.2 seed u) I≠0) :
    I≠0 ∧ (I.absNorm:ℝ)≤
      (∏i,upper i)*b₁*b₂*((X₁*X₂)/pairNorm d)*(∏i,P i) := by
  obtain ⟨u,hu,hune,huI⟩ := finiteColumnCoefficient_witness Q _ I hI
  have hp := (mul_ne_zero_iff.mp hune).2
  have hn := profileCoefficient_product_bound R ν Wslot P upper W₁ W₂ b₁ b₂
    X₁ X₂ Y₁ Y₂ (X₁*X₂) d.1 d.2 seed hP hX₁ hX₂ hY₁ hY₂ hd.1 hd.2
    rfl hXY.symm hz hz₁ hz₂ hs hs₁ hs₂ u hp
  rw [huI] at hn
  exact hn

/-- The actual canonical support radius. Equal rectangle products let
both ordinary branches use T, rather than a product of separate maxima. -/
def sourceNormCap (P : α→ℝ) (b T : ℝ) (d : Id×Id) : ℝ :=
  b^2*(T/pairNorm d)*(∏i,2*P i)

/-- Full original-column norm cap, with the literal tupleWeight and
the actual finite sourcePools. The hypotheses are just the already
specified compact profile supports and positive original scales. -/
theorem original_column_norm
    (S H : Finset PrimeIdeal) (pool : α→Finset Id)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (R seed : Id) (ν : α→Id→ℂ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (σ freq P : α→ℝ) (hP : ∀i,0<P i)
    (W₁ W₂ : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc a b)
    (t₁ t₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hXY : X₁*X₂=Y₁*Y₂) (I : Id)
    (hI : originalColumn S H pool d hd R seed ν (fun i=>slotProfile W (σ i) (freq i)) P
      (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b X₁ X₂ Y₁ Y₂ I≠0) :
    I≠0 ∧ (I.absNorm:ℝ)≤sourceNormCap P b (X₁*X₂) d := by
  have hslot (i : α) : Function.support (slotProfile W (σ i) (freq i))⊆Set.Icc (1:ℝ) 2 :=
    (slot_profile_support W (σ i) (freq i)).trans hWs
  have hphase₁ : Function.support (phaseProfile W₁ t₁)⊆Set.Icc a b :=
    (phaseProfile_support W₁ t₁).trans hs₁
  have hphase₂ : Function.support (phaseProfile W₂ t₂)⊆Set.Icc a b :=
    (phaseProfile_support W₂ t₂).trans hs₂
  have hz (i : α) : slotProfile W (σ i) (freq i) 0=0 := by
    by_contra hn
    have hh := (hslot i hn).1
    norm_num at hh
  have hz₁ : phaseProfile W₁ t₁ 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hphase₁ hn).1
  have hz₂ : phaseProfile W₂ t₂ 0=0 := by
    by_contra hn
    exact (not_le_of_gt ha) (hphase₂ hn).1
  have hn := weighted_profile_column_norm
    (Fintype.piFinset (sourcePools pool d hd b X₁ X₂ Y₁ Y₂)) (tupleWeight (punctureProduct S H))
    R seed ν (fun i=>slotProfile W (σ i) (freq i)) P (fun _=>(2:ℝ))
    (phaseProfile W₁ t₁) (phaseProfile W₂ t₂) b b X₁ X₂ Y₁ Y₂ d hd
    hP hX₁ hX₂ hY₁ hY₂ hXY hz hz₁ hz₂
    (fun i x hx=>(hslot i hx).2) (fun x hx=>(hphase₁ hx).2) (fun x hx=>(hphase₂ hx).2) I hI
  refine ⟨hn.1,hn.2.trans_eq ?_⟩
  unfold sourceNormCap
  rw [Finset.prod_mul_distrib]
  ring

omit [Fintype α] in
/-- A nonzero residual coefficient supplies a genuine full-norm cap on
G, I and the artificial divisor D. In fact N(G)*N(D) has the same cap.
This finite support fact is valid for prime-power common ideals. -/
theorem residual_norm_gates (β : Id→ℂ) (Hsource : ℝ)
    (hcap : ∀J,β J≠0→J≠0 ∧ (J.absNorm:ℝ)≤Hsource)
    (G D I : Id) (hI : (if IsCoprime G I ∧ D∣I then β (G*I) else 0)≠0) :
    G≠0 ∧ D≠0 ∧ I≠0 ∧ (G.absNorm:ℝ)≤Hsource ∧ (D.absNorm:ℝ)≤Hsource ∧
      (I.absNorm:ℝ)≤Hsource ∧ (G.absNorm:ℝ)*(D.absNorm:ℝ)≤Hsource := by
  have hm : IsCoprime G I ∧ D∣I := by
    by_contra hn
    exact hI (by rw [if_neg hn])
  have hβ : β (G*I)≠0 := by simpa only [if_pos hm] using hI
  have hc := hcap (G*I) hβ
  have hG : G≠0 := by
    intro h
    exact hc.1 (by rw [h,zero_mul])
  have hIn : I≠0 := by
    intro h
    exact hc.1 (by rw [h,mul_zero])
  have hD : D≠0 := by
    intro h
    have hh := hm.2
    rw [h,zero_dvd_iff] at hh
    exact hIn hh
  have hg := (CenteredExceptionalCount.norm_le_of_dvd hc.1 (dvd_mul_right G I)).trans hc.2
  have hi := (CenteredExceptionalCount.norm_le_of_dvd hc.1 (dvd_mul_left I G)).trans hc.2
  have hdv := (CenteredExceptionalCount.norm_le_of_dvd hIn hm.2).trans hi
  have hgd : G*D∣G*I := by
    obtain ⟨J,hJ⟩ := hm.2
    refine ⟨J,?_⟩
    rw [hJ,mul_assoc]
  have hprod := (CenteredExceptionalCount.norm_le_of_dvd hc.1 hgd).trans hc.2
  refine ⟨hG,hD,hIn,hg,hdv,hi,?_⟩
  simpa only [map_mul,Nat.cast_mul] using hprod

/-- An explicit power cap for the full original source norm. The fixed
compact-profile and slot-count factor is absorbed by the displayed lower
bound on Z; prime-power divisor norms are not replaced by radicals. -/
theorem sourceNormCap_power_bound (Z b T L M : ℝ) (w : α→ℝ)
    (d : Id×Id) (hd : d.1≠0 ∧ d.2≠0) (hZ : 1≤Z)
    (hconstant : b^2*2^(Fintype.card α)≤Z)
    (hT : 0≤T) (hTL : T≤Z^L) (hslots : (∑i,w i)≤M) :
    sourceNormCap (fun i=>Z^(w i)) b T d≤Z^(1+L+M) := by
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ
  have hdn : (1:ℝ)≤pairNorm d := by
    have hnorm : (1:ℝ)≤((d.1*d.2).absNorm:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (mul_ne_zero hd.1 hd.2))
    simpa only [pairNorm,map_mul,Nat.cast_mul] using hnorm
  have hTdiv : T/pairNorm d≤Z^L := (div_le_self hT hdn).trans hTL
  have hpow : Z^(∑i,w i)≤Z^M :=
    Real.rpow_le_rpow_of_exponent_le hZ hslots
  have hprod : (∏i,2*Z^(w i))=2^(Fintype.card α)*Z^(∑i,w i) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,
      ←Real.rpow_sum_of_pos hZ0]
  unfold sourceNormCap
  rw [hprod]
  calc
    _ = (b^2*2^(Fintype.card α))*(T/pairNorm d)*Z^(∑i,w i) := by ring
    _ ≤ Z*Z^L*Z^M := mul_le_mul
      (mul_le_mul hconstant hTdiv
        (div_nonneg hT (pairNorm_pos hd.1 hd.2).le) hZ0.le)
      hpow (Real.rpow_nonneg hZ0.le _) (mul_nonneg hZ0.le (Real.rpow_nonneg hZ0.le _))
    _ = _ := by rw [Real.rpow_add hZ0,Real.rpow_add hZ0,Real.rpow_one]

/-- The preceding explicit threshold is uniform over all slot widths,
prefix divisors and scales satisfying the fixed power budgets. -/
theorem eventually_sourceNormCap_power (b L M : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1≤Z ∧
      ∀(w : α→ℝ)(T : ℝ)(d : Id×Id),d.1≠0 → d.2≠0 →
        0≤T → T≤Z^L → (∑i,w i)≤M →
        sourceNormCap (fun i=>Z^(w i)) b T d≤Z^(1+L+M) := by
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),
    Filter.eventually_ge_atTop (b^2*2^(Fintype.card α))] with Z hZ hconstant
  refine ⟨hZ,?_⟩
  intro w T d hd₁ hd₂ hT hTL hw
  exact sourceNormCap_power_bound Z b T L M w d ⟨hd₁,hd₂⟩ hZ hconstant hT hTL hw

end
end Candidate.SilPrior.FourthPower.MixedOriginalNormCap
