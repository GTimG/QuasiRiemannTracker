/- Copyright (c) 2026 Sil. Apache-2.0.
Reference choices AFTER full-support seed allocation and ordinary rebasing.
This module proves the choices, exact finite centering/orientation, and the
actual frozen scalar payment. It does not assert the still-unassembled
whole-source mixed-moment theorem.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstRebase
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstPaidCosts
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferencePuncturedReference
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.ReferenceExtractionGeometry
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedCanonicalSource
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedDivisorMask
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.UncenteredTerminal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstReferenceChoice
noncomputable section
open scoped Classical BigOperators ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CanonicalRowCompletion
open QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentRectangle CenteredMomentUncenteredTerminal CenteredMomentCommonRawScale
open CenteredMomentCommonRawCost CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open MixedCommonAllocation MixedCommonCoefficient MixedCommonRestriction MixedTupleRows
open MixedSourceAssembly MixedLiveNormalization MixedDivisorMask MixedCanonicalSource
local notation "Id" => Ideal HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- This is the actual H-zero provenance used by the reference theorem.
It follows from canonical deletion, not from an extra estimate of a row. -/
theorem canonical_hole_zero (ν : ι → Character) (R₀ : ι → Finset Id)
    (t : ℝ) (H : Finset PrimeIdeal) (hHR : ∀i,∀Q∈H,Q.val∈R₀ i)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (i : ι) (Q : PrimeIdeal) (hQ : Q∈H) :
    slotCoefficient ν R₀ t i Q.val*Wslot i (Q.val.absNorm/P i)=0 := by
  simp only [slotCoefficient,CenteredMomentCommonMaskEnergy.heightCoefficient,
    NativeFiniteHoles.holeCoefficient,hHR i Q hQ,ite_true,zero_mul]

theorem comparison_scale_le_half (b : ℝ) : comparisonScale b ≤ 1/2 := by
  have hm : 1 ≤ max 1 b := le_max_left _ _
  unfold comparisonScale
  apply (div_le_iff₀ (by positivity : 0<2*max 1 b)).mpr
  nlinarith

/-- An original factor shorter than the subunit comparison scale is
identically zero, including the zero ideal. No lower-length assumption
has been silently added to the uncentered branch. -/
theorem small_scale_zero (W : ℝ → ℂ) (a b X : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hX : 0<X)
    (hsmall : X ≤ comparisonScale b) (B I : Id) (hB : B ≠ 0) :
    W ((Ideal.absNorm (B*I):ℝ)/X)=0 := by
  by_contra hn
  have ht := hs hn
  by_cases hI : I=0
  · simp only [hI,mul_zero,map_zero,Nat.cast_zero,zero_div,Set.mem_Icc] at ht
    linarith [ht.1]
  have hN : 1 ≤ (Ideal.absNorm (B*I):ℝ) :=
    QuadraticMainBoundary.norm_one_le (mul_ne_zero hB hI)
  have hb : 0 ≤ b := le_trans (le_of_lt (div_pos (zero_lt_one.trans_le hN) hX)) ht.2
  have hu : (Ideal.absNorm (B*I):ℝ) ≤ b*X := (div_le_iff₀ hX).mp ht.2
  have hm : 0<max 1 b := zero_lt_one.trans_le (le_max_left _ _)
  have he : max 1 b*comparisonScale b=1/2 := by
    unfold comparisonScale
    field_simp [hm.ne']
  have hc : b*comparisonScale b ≤ 1/2 := by
    rw [←he]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (comparisonScale_pos b).le
  have hh := (mul_le_mul_of_nonneg_left hsmall hb).trans hc
  linarith

theorem uncentered_small_factor (R : Id) (ν : ι → Id → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (a b X₁ X₂ : ℝ) (ha : 0<a)
    (hs₁ : Function.support W₁⊆Set.Icc a b)
    (hs₂ : Function.support W₂⊆Set.Icc a b)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (B₁ B₂ seed : Id) (hB₁ : B₁ ≠ 0) (hB₂ : B₂ ≠ 0)
    (hsmall : X₁ ≤ comparisonScale b ∨ X₂ ≤ comparisonScale b) (v : Tuple ι) :
    uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ seed v=0 := by
  rcases hsmall with h|h
  · have hz := small_scale_zero W₁ a b X₁ ha hs₁ hX₁ h B₁ (v (Sum.inr 0)) hB₁
    simp only [uncenteredProfileCoefficient,hz,zero_mul,mul_zero]
  · have hz := small_scale_zero W₂ a b X₂ ha hs₂ hX₂ h B₂ (v (Sum.inr 1)) hB₂
    simp only [uncenteredProfileCoefficient,hz,zero_mul,mul_zero]

/-- The uncentered embedding has L=c, not L=1. Its equal-product
reference vanishes by comparison_first_zero/profileCoefficient_eq_uncentered. -/
theorem uncentered_geometry (b X₁ X₂ T : ℝ) (hprod : X₁*X₂=T)
    (h₁ : comparisonScale b ≤ X₁) (h₂ : comparisonScale b ≤ X₂) :
    0<comparisonScale b ∧ comparisonScale b*(T/comparisonScale b)=T ∧
      comparisonScale b ≤ X₁ ∧ comparisonScale b ≤ X₂ ∧
      comparisonScale b ≤ T/comparisonScale b := by
  have hc := comparisonScale_pos b
  refine ⟨hc,comparison_product b T,h₁,h₂,?_⟩
  apply (le_div_iff₀ hc).mpr
  rw [←hprod]
  exact mul_le_mul h₁ h₂ hc.le (hc.le.trans h₁)

/-- Rebased ordinary scales may have negative total logarithmic width.
Only the centered branch forces a positive reference exponent. -/
theorem centered_geometry (Z P l X₁ X₂ : ℝ) (hZ : 1 ≤ Z)
    (hprod : X₁*X₂=Z^P) (hl : 0 ≤ l) (hlP : 2*l ≤ P)
    (h₁ : Z^l ≤ X₁) (h₂ : Z^l ≤ X₂) :
    0<Z^l ∧ Z^l*((X₁*X₂)/Z^l)=X₁*X₂ ∧
      Z^l ≤ X₁ ∧ Z^l ≤ X₂ ∧ Z^l ≤ (X₁*X₂)/Z^l := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpower : 0<Z^l := Real.rpow_pos_of_pos hZp l
  refine ⟨hpower,by field_simp [hpower.ne'],h₁,h₂,?_⟩
  apply (le_div_iff₀ hpower).mpr
  rw [hprod,←Real.rpow_add hZp]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem short_complement (Z P l X₁ X₂ : ℝ) (hZ : 0<Z)
    (hX₂ : 0<X₂) (hprod : X₁*X₂=Z^P) (hshort : X₁ ≤ Z^l) :
    Z^(P-l) ≤ X₂ := by
  rw [Real.rpow_sub hZ]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hZ l)).mpr
  rw [←hprod,mul_comm X₂]
  exact mul_le_mul_of_nonneg_right hshort hX₂.le

/-- The actual geometric three-way split. Short-right is deliberately
retained as a separate orientation until the exact swap identity below. -/
theorem centered_choice (Z R P s d X₁ X₂ : ℝ) (hZ : 1 ≤ Z)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hcap : P+2*s+4*d<R)
    (hcenter : (5/6)*R-(7/3)*d<P+s) (hprod : X₁*X₂=Z^P) :
    ∃l : ℝ,0<l ∧ l<P/2 ∧
      R+d+2*l-P+s<R/2 ∧ l+(R+d)/2+s<(4/5)*R ∧
      (X₁<Z^l ∨ X₂<Z^l ∨
        (Z^l ≤ X₁ ∧ Z^l ≤ X₂ ∧ Z^l ≤ (X₁*X₂)/Z^l ∧
          Z^l*((X₁*X₂)/Z^l)=X₁*X₂)) := by
  obtain ⟨l,hl,hu⟩ := MixedLedger.reference_interval_nonempty hcap
  have hg := MixedLedger.reference_gate hs hd hcap hcenter hl hu
  refine ⟨l,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,?_⟩
  by_cases h₁ : X₁<Z^l
  · exact Or.inl h₁
  by_cases h₂ : X₂<Z^l
  · exact Or.inr (Or.inl h₂)
  have hh := centered_geometry Z P l X₁ X₂ hZ hprod hg.1.le
    (by linarith [hg.2.1]) (le_of_not_gt h₁) (le_of_not_gt h₂)
  exact Or.inr (Or.inr ⟨hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hh.2.1⟩)

/-- A fixed inherited reserve gives ONE cutoff/constant allowance for
all shortened live sources. It is not necessary to choose a new analytic
loss or a new profile constant after seeing the allocation. -/
theorem centered_midpoint_margin (R P s d ρ : ℝ) (hρ : 0<ρ)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hcap : P+2*s+4*d ≤ R-ρ)
    (hcenter : 5*R/6-7*d/3<P+s) :
    ∃l : ℝ,MixedFirstPaidCosts.ReferenceChoice R P s d l ∧
      0<l ∧ l<P/2 ∧
      l+(R+d)/2+s+2*(ρ/100) ≤ (4/5)*R ∧
      R+d+2*l-P+s+2*(ρ/100) ≤ R/2 := by
  let l := (MixedLedger.lower R P s d+MixedLedger.upper R P s d)/2
  have hl : MixedLedger.lower R P s d<l := by
    dsimp [l,MixedLedger.lower,MixedLedger.upper]
    linarith
  have hu : l<MixedLedger.upper R P s d := by
    dsimp [l,MixedLedger.lower,MixedLedger.upper]
    linarith
  have hg := MixedLedger.reference_gate hs hd (by linarith : P+2*s+4*d<R)
    (by linarith : (5/6)*R-(7/3)*d<P+s) hl hu
  refine ⟨l,Or.inr ⟨hcenter,hl,hu⟩,hg.1,hg.2.1,?_,?_⟩ <;>
    dsimp [l,MixedLedger.lower,MixedLedger.upper] at * <;> linarith

/-- Connect the chosen exponent to the SAME ReferenceChoice consumed by
the checked sixteen-pair payment. In the uncentered case the actual
minimum is c; the centered case uses minimum Z^l only after the short
original branches have been removed. -/
theorem reference_choice_dispatch (Z R P s d l b X₁ X₂ : ℝ)
    (hZ : 1 ≤ Z) (hs : 0 ≤ s) (hd : 0 ≤ d) (hcap : P+2*s+4*d<R)
    (hprod : X₁*X₂=Z^P)
    (href : MixedFirstPaidCosts.ReferenceChoice R P s d l) :
    (l=0 ∧ P+s ≤ 5*R/6-7*d/3 ∧
      (X₁ ≤ comparisonScale b ∨ X₂ ≤ comparisonScale b ∨
        (comparisonScale b ≤ X₁ ∧ comparisonScale b ≤ X₂ ∧
          comparisonScale b ≤ (X₁*X₂)/comparisonScale b ∧
          comparisonScale b*((X₁*X₂)/comparisonScale b)=X₁*X₂))) ∨
    (0<l ∧ l<P/2 ∧ R+d+2*l-P+s<R/2 ∧ l+(R+d)/2+s<(4/5)*R ∧
      (X₁<Z^l ∨ X₂<Z^l ∨
        (Z^l ≤ X₁ ∧ Z^l ≤ X₂ ∧ Z^l ≤ (X₁*X₂)/Z^l ∧
          Z^l*((X₁*X₂)/Z^l)=X₁*X₂))) := by
  rcases href with ⟨hl,hthreshold⟩|⟨hcenter,hl,hu⟩
  · apply Or.inl
    refine ⟨hl,hthreshold,?_⟩
    by_cases h₁ : X₁ ≤ comparisonScale b
    · exact Or.inl h₁
    by_cases h₂ : X₂ ≤ comparisonScale b
    · exact Or.inr (Or.inl h₂)
    have hh := uncentered_geometry b X₁ X₂ (X₁*X₂) rfl
      (le_of_not_ge h₁) (le_of_not_ge h₂)
    exact Or.inr (Or.inr ⟨hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hh.2.1⟩)
  · apply Or.inr
    have hg := MixedLedger.reference_gate hs hd hcap (by linarith :
      (5/6)*R-(7/3)*d<P+s) hl hu
    refine ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2,?_⟩
    by_cases h₁ : X₁<Z^l
    · exact Or.inl h₁
    by_cases h₂ : X₂<Z^l
    · exact Or.inr (Or.inl h₂)
    have hh := centered_geometry Z P l X₁ X₂ hZ hprod hg.1.le
      (by linarith [hg.2.1]) (le_of_not_gt h₁) (le_of_not_gt h₂)
    exact Or.inr (Or.inr ⟨hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,hh.2.1⟩)

/-- The two strict mixed gates survive full support allocation and
rebasing, before any choice of reference. No lower bound on P' is used. -/
theorem shortened_gates (R P s d P' s' : ℝ)
    (hP : P' ≤ P) (hs : s' ≤ s) (hcap : P+2*s+4*d<R) (hslot : (3/4)*s<d) :
    P'+2*s'+4*d<R ∧ (3/4)*s'<d := by constructor <;> linarith

/-- These are the two literal length hypotheses of punctured_reference,
derived for the shorter oriented ordinary factor. They also apply to the
equal-product reference itself by taking X1=Z^l. -/
theorem short_reference_caps (Z R P s d l δ xi b U X₁ X₂ slotFactor V : ℝ)
    (hZ : 1 ≤ Z) (hb : 0 ≤ b) (hU : 0 ≤ U) (hslot : 0 ≤ slotFactor) (hV : 0 ≤ V)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hprod : X₁*X₂=Z^P)
    (hshort : X₁ ≤ Z^l) (hUcap : U ≤ Z^(R+d)) (hVcap : V ≤ slotFactor*Z^s)
    (hfixed : (b+4)*b*slotFactor ≤ Z^δ) (hxi : xi/2 ≤ δ) :
    (b+4)*Z^(xi/2)*b*X₁*V*Real.sqrt U ≤ Z^(l+(R+d)/2+s+2*δ) ∧
      (b+4)*Z^(xi/2)*b*(X₁*V*U/X₂) ≤ Z^(R+d+2*l-P+s+2*δ) := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hcomplement := short_complement Z P l X₁ X₂ hZp hX₂ hprod hshort
  have hphase : Z^(xi/2) ≤ Z^δ := Real.rpow_le_rpow_of_exponent_le hZ hxi
  have hC : 0 ≤ (b+4)*b := by positivity
  constructor
  · calc
      _=((b+4)*b)*Z^(xi/2)*X₁*V*Real.sqrt U := by ring
      _ ≤ ((b+4)*b)*Z^(xi/2)*Z^l*(slotFactor*Z^s)*Real.sqrt (Z^(R+d)) := by gcongr
      _=((b+4)*b*slotFactor)*Z^(xi/2)*Z^l*Z^s*Real.sqrt (Z^(R+d)) := by ring
      _ ≤ Z^δ*Z^δ*Z^l*Z^s*Real.sqrt (Z^(R+d)) := by gcongr
      _=Z^(l+(R+d)/2+s+2*δ) := by
        rw [ReferenceExtractionGeometry.sqrt_power Z (R+d) hZp.le]
        simp_rw [←Real.rpow_add hZp]
        congr 1
        ring
  · calc
      _=((b+4)*b)*Z^(xi/2)*(X₁*V*U/X₂) := by ring
      _ ≤ ((b+4)*b)*Z^(xi/2)*(Z^l*(slotFactor*Z^s)*Z^(R+d)/Z^(P-l)) := by gcongr
      _=((b+4)*b*slotFactor)*Z^(xi/2)*(Z^l*Z^s*Z^(R+d)/Z^(P-l)) := by ring
      _ ≤ Z^δ*Z^δ*(Z^l*Z^s*Z^(R+d)/Z^(P-l)) := by gcongr
      _=Z^(R+d+2*l-P+s+2*δ) := by
        rw [←Real.rpow_add hZp l s,←Real.rpow_add hZp (l+s) (R+d),
          ←Real.rpow_sub hZp,←Real.rpow_add hZp δ δ,←Real.rpow_add hZp]
        congr 1
        ring

open Set ReferenceFactors ReferenceHeckeProducts ReferencePrimeEnclosure
open KernelAssignmentReindex KernelMarkedRows KernelLabelledSlots KernelRowExpansion
open KernelRowProfiles KernelRowPools KernelPunctureRows CenteredMomentScaleSupremum

/-- Genuine short/reference energy, supplied by the already checked
punctured reference theorem. The two sharp length gates are derived above.
Canonical deleted coefficients supply the H-zero condition internally.

This is a seed-one live-row endpoint: the exact finite seed allocation and
the scalar payment below must precede its whole-source application. -/
theorem short_punctured_reference (ε L K a b xi Bf : ℝ)
    (hε : 0<ε) (hL : 0<L) (hK : 0<K) (ha : 0<a)
    (hb : 0 ≤ b) (hxi : 0<xi) (hBf : 1 ≤ Bf) :
    ∃n : ℕ,∀Wlong : ℝ → ℂ,
      Function.support Wlong⊆Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀Z R P s d l δ : ℝ,
      1 ≤ Z → 0 ≤ R → 0 ≤ s → 0 ≤ d → 0 ≤ l → 0 ≤ δ → P+2*s+4*d<R →
      R+(l+(R+d)/2+s+2*δ) ≤ L →
      l+(R+d)/2+s+2*δ ≤ (4/5)*R → R+d+2*l-P+s+2*δ ≤ R/2 →
      (b+4)*b*(2:ℝ)^Fintype.card ι ≤ Z^δ → xi/2 ≤ δ →
      ∀(η : Character)(m D₀ : HeckeFamily.O)(rows : Finset HeckeFamily.O)(χ : rows → Character),
      (∀x I,Supported I → idealCoeff (χ x) I=fixedCoefficient η m D₀ I*idealRowHom x.val I) →
      (∀x I,¬Supported I → idealCoeff (χ x) I=0) →
      (∀x∈rows,(Ideal.absNorm (Ideal.span {x}):ℝ) ≤ Z^R) →
      (∀i,(χ i).residue ≠ 1) →
      ∀(U X₁ X₂ Height t₁ t₂ : ℝ)(Wshort : ℝ → ℂ)(B : ℝ),
      1 ≤ U → U ≤ Z^K → U ≤ Z^(R+d) → 0<X₁ → 0<X₂ → X₁*X₂=Z^P → X₁ ≤ Z^l →
      0 ≤ Height → ‖t₂‖ ≤ Height → (∀i,((χ i).modulus.absNorm:ℝ) ≤ U) →
      0 ≤ B → Function.support Wshort⊆Icc a b → ContDiff ℝ ∞ Wshort →
      (∀(j : Fin 2)(x : ℝ),‖scaleTest Wshort j x‖ ≤ B) →
      ∀(S H : Finset PrimeIdeal)(F : Id),F ≠ 0 → (F.absNorm:ℝ) ≤ Z^K →
      (∀Q∈H,Q.val∣F) →
      (∀Q∈S,Supported Q.val ∧ (Q.val.absNorm:ℝ) ≤ Z^K) →
      (∀I,Supported I → ((I.absNorm:ℝ) ≤ b*X₁ ∨ (I.absNorm:ℝ) ≤ b*X₂) →
        primeSupport I⊆primeValues S) →
      ∀(pool : ι → Finset Id)(ν : ι → Character)(R₀ : ι → Finset Id)
        (t : ℝ)(Wslot : ι → ℝ → ℂ)(scales : ι → ℝ),
      (∀i,0<scales i) →
      (∀i I,I∈pool i → Supported I ∧ (I.absNorm:ℝ) ≤ 2*scales i) →
      (∀i I,I∈pool i → ‖slotCoefficient ν R₀ t i I*Wslot i (I.absNorm/scales i)‖ ≤ Bf) →
      (∀i,∀Q∈H,Q.val∈R₀ i) →
      (∏i,2*scales i) ≤ Z^L → b*X₁*(∏i,2*scales i) ≤ Z^L →
      (∏i,scales i) ≤ Z^s →
      (∑i : rows,‖weightedSum
        (naturalCoefficients (χ i) S pool
          (fun j I=>slotCoefficient ν R₀ t j I*Wslot j (I.absNorm/scales j)) scales)
        (fun slot=>normalizedRow (χ i) (supportedRectangle S b X₁ X₂)
          (restrictedValue S (augmented S H (marked S slot)))
          (phaseProfile Wshort t₁) (phaseProfile Wlong t₂) X₁ X₂)‖^2) ≤
        C*(1+Height)^(2*n)*Z^(R+ε)*B^2 := by
  obtain ⟨n,hn⟩ := ReferencePuncturedReference.punctured_reference (α:=ι)
    ε L K a b xi Bf hε hL hK ha hb hxi hBf
  refine ⟨n,?_⟩
  intro Wlong hlong hsmooth
  obtain ⟨C,hC,hbound⟩ := hn Wlong hlong hsmooth
  refine ⟨C,hC,?_⟩
  intro Z R P s d l δ hZ hR hs hd hl hδ hcap htotal hmax href hfixed hξ
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hUsharp hX₁ hX₂ hprod hshort
    hHeight ht₂ hmod hB hWs hWsm htest S H F hF hFcap hH hS henclose
    pool ν R₀ t Wslot scales hP hp hβ hHR hVcap hvolume hVsharp
  have hnonneg := ReferenceExtractionGeometry.mixed_exponents_nonneg
    R P s d l hR hs hd hl hcap
  have hslot : (∏i,2*scales i) ≤ (2:ℝ)^Fintype.card ι*Z^s := by
    rw [Finset.prod_mul_distrib]
    simpa only [Finset.prod_const,Finset.card_univ] using
      mul_le_mul_of_nonneg_left hVsharp (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
  have hc := short_reference_caps Z R P s d l δ xi b U X₁ X₂
    ((2:ℝ)^Fintype.card ι) (∏i,2*scales i)
    hZ hb (zero_le_one.trans hU) (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    (Finset.prod_nonneg (fun i _=>by have := hP i;positivity))
    hX₁ hX₂ hprod hshort hUsharp hslot hfixed hξ
  exact hbound Z R (l+(R+d)/2+s+2*δ) (R+d+2*l-P+s+2*δ)
    hZ hR (by linarith [hnonneg.1]) (by linarith [hnonneg.2]) htotal hmax href
    η m D₀ rows χ hon hoff hrows hnonprincipal
    U X₁ X₂ Height t₁ t₂ Wshort B hU hUcap hX₁ hX₂ hHeight ht₂ hmod hB hWs hWsm htest
    S H F hF hFcap hH hS henclose pool
    (fun i I=>slotCoefficient ν R₀ t i I*Wslot i (I.absNorm/scales i)) scales
    hP hp hβ (canonical_hole_zero ν R₀ t H hHR Wslot scales)
    hVcap hvolume hc.1 hc.2

/-- Centering keeps the literal whole-column seed and both coprimality
and tuple restrictions. It is an equality before any squared norm. -/
theorem profile_centering (R : Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ)
    (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ seed : Id)
    (v : Tuple ι) :
    uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ seed v=
      profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v+
        uncenteredProfileCoefficient R ν Wslot P W₁ W₂ Y₁ Y₂ B₁ B₂ seed v := by
  unfold uncenteredProfileCoefficient profileCoefficient idealRectangle
  ring

theorem finite_centering (F : Finset (Tuple ι)) (H R : Id)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ seed : Id) (ψ : Id → ℂ) :
    (∑v∈F,tupleWeight H v*
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ seed v*
        ψ (finiteTupleProduct v))=
      (∑v∈F,tupleWeight H v*
        profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v*
          ψ (finiteTupleProduct v))+
      (∑v∈F,tupleWeight H v*
        uncenteredProfileCoefficient R ν Wslot P W₁ W₂ Y₁ Y₂ B₁ B₂ seed v*
          ψ (finiteTupleProduct v)) := by
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [profile_centering R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v]
  ring

theorem packed_weight_swap (H : Id) (p : ι → Id) (A B : Id) :
    tupleWeight H (pack p (A,B))=tupleWeight H (pack p (B,A)) := by
  unfold tupleWeight tupleRestriction restriction slotProduct
  simp only [pack,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [mul_comm A B]

theorem packed_profile_swap (R : Id) (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ)
    (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (B₁ B₂ seed : Id)
    (p : ι → Id) (A B : Id) :
    uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ seed (pack p (A,B))=
      uncenteredProfileCoefficient R ν Wslot P W₂ W₁ X₂ X₁ B₂ B₁ seed (pack p (B,A)) := by
  simp only [uncenteredProfileCoefficient,pack_product]
  rw [mul_comm B A]
  simp only [pack,Sum.elim_inl,Sum.elim_inr,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

/-- Orient the actual short ordinary factor first. The finite domains,
whole-column phase, seed, and ordinary puncture are reindexed exactly. -/
theorem finite_swap (pool : ι → Finset Id) (A B : Finset Id) (H R : Id)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (B₁ B₂ seed : Id) (ψ : Id → ℂ) :
    (∑v∈Fintype.piFinset (pools pool A B),tupleWeight H v*
      uncenteredProfileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ B₁ B₂ seed v*
        ψ (finiteTupleProduct v))=
      ∑v∈Fintype.piFinset (pools pool B A),tupleWeight H v*
        uncenteredProfileCoefficient R ν Wslot P W₂ W₁ X₂ X₁ B₂ B₁ seed v*
          ψ (finiteTupleProduct v) := by
  rw [split_tuple_sum,split_tuple_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [packed_weight_swap,packed_profile_swap,pack_product,pack_product,mul_comm I J]

/-- The seed payment needed by the final source is the full reciprocal
N(seed), not N(seed)^(-2/3). This is the actual frozen amplitude and the
actual normalization. Reference choices must follow this allocation. -/
theorem seed_frozen_cost (H R seed : Id) (hseed : Squarefree seed)
    (a : Allocation seed (Finset.univ : Finset (ι⊕Fin 2)))
    (B : Tuple ι) (hB : ∀j,B j ≠ 0)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖ ≤ 1)
    (hWnorm : ∀i x,‖Wslot i x‖ ≤ M i) (hM : ∀i,1 ≤ M i)
    (hW : ∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2) :
    ‖frozenWeight H B*allocationTerm seed Finset.univ B a*
      frozenCoefficient B (finiteTupleProduct B) R ν Wslot P‖^2/rawReduction B P ≤
        (∏i,M i)^2*(2:ℝ)^Fintype.card ι/(seed.absNorm:ℝ) := by
  have hseedpos : 0<(seed.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hseed.ne_zero)
  have hraw := rawReduction_pos B hB P hP
  by_cases hz : allocationTerm seed Finset.univ B a=0
  · simp only [hz,mul_zero,zero_mul,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div]
    positivity
  have hprod : finiteTupleProduct B ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
  have hn := (squarefree_norm_le_selected_product seed hseed a).trans
    (selected_product_norm seed a B hB hz)
  have hf := frozen_normalized_cost B hB (finiteTupleProduct B) R hprod rfl
    ν Wslot P M hP hν hWnorm hM 1 2 zero_lt_one hW
  rw [max_eq_right (by norm_num : (1:ℝ) ≤ 2)] at hf
  have hnorm : ‖frozenWeight H B*allocationTerm seed Finset.univ B a*
      frozenCoefficient B (finiteTupleProduct B) R ν Wslot P‖ ≤
      ‖frozenCoefficient B (finiteTupleProduct B) R ν Wslot P‖ := by
    rw [mul_assoc]
    apply (MixedCommonEnergy.frozen_scalar_norm_le H B _).trans
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (allocation_term_norm seed Finset.univ B a) (norm_nonneg _)
  apply (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hraw.le).trans
  exact hf.trans (div_le_div_of_nonneg_left (by positivity) hseedpos hn)

/-- The original prefix is paid exactly once outside the rebased
normalization. Its full pair norm is preserved. -/
theorem seed_frozen_cost_with_prefix (H R seed : Id) (hseed : Squarefree seed)
    (a : Allocation seed (Finset.univ : Finset (ι⊕Fin 2)))
    (B : Tuple ι) (hB : ∀j,B j ≠ 0) (d : Id×Id) (hd : d.1 ≠ 0 ∧ d.2 ≠ 0)
    (ν : ι → Id → ℂ) (Wslot : ι → ℝ → ℂ) (P M : ι → ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖ ≤ 1)
    (hWnorm : ∀i x,‖Wslot i x‖ ≤ M i) (hM : ∀i,1 ≤ M i)
    (hW : ∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2) :
    (‖frozenWeight H B*allocationTerm seed Finset.univ B a*
      frozenCoefficient B (finiteTupleProduct B) R ν Wslot P‖^2/rawReduction B P)/pairNorm d ≤
        (∏i,M i)^2*(2:ℝ)^Fintype.card ι/(pairNorm d*(seed.absNorm:ℝ)) := by
  have hh := div_le_div_of_nonneg_right
    (seed_frozen_cost H R seed hseed a B hB ν Wslot P M hP hν hWnorm hM hW)
    (pairNorm_pos hd.1 hd.2).le
  exact hh.trans_eq (by ring)

/-- Both actual finite Cauchy counts are paid before any physical row or
selected D. The output retains the full reciprocal seed norm. This is a
numerical scalar theorem, not an assumed estimate for the live energies. -/
theorem uniform_seed_scalar_mass (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧
    ∀(S : (ι⊕Fin 2) → Finset Id)(H R seed : Id),Squarefree seed →
    ∀(ν : ι → Id → ℂ)(Wslot : ι → ℝ → ℂ)(P M : ι → ℝ),
      (∀i,0<P i) → (∀i I,‖ν i I‖ ≤ 1) →
      (∀i x,‖Wslot i x‖ ≤ M i) → (∀i,1 ≤ M i) →
      (∀i,Function.support (Wslot i)⊆Set.Icc (1:ℝ) 2) →
      ((Fintype.card (Allocation seed (Finset.univ : Finset (ι⊕Fin 2))):ℝ)*
        (MixedFixedSupport.boundedLabels S seed).card)*
        (∑a : Allocation seed (Finset.univ : Finset (ι⊕Fin 2)),
          ∑B : MixedFixedSupport.boundedLabels S seed,
            ‖frozenWeight H B.val*allocationTerm seed Finset.univ B.val a*
              frozenCoefficient B.val (finiteTupleProduct B.val) R ν Wslot P‖^2/
                rawReduction B.val P) ≤
      C*(seed.absNorm:ℝ)^ε*((∏i,M i)^2*(2:ℝ)^Fintype.card ι)/(seed.absNorm:ℝ) := by
  have hdim : 0<Fintype.card (ι⊕Fin 2) := Fintype.card_pos
  obtain ⟨Ca,hCa,hacount⟩ := allocation_count_squared (Fintype.card (ι⊕Fin 2))
    hdim (ε/2) (half_pos hε)
  obtain ⟨Cb,hCb,hbcount⟩ := fixed_count_squared (ι:=ι⊕Fin 2) (ε/2) (half_pos hε)
  refine ⟨Ca*Cb,mul_pos hCa hCb,?_⟩
  intro S H R seed hseed ν Wslot P M hP hν hWnorm hM hW
  let A := (Fintype.card (Allocation seed (Finset.univ : Finset (ι⊕Fin 2))):ℝ)
  let Bn := ((MixedFixedSupport.boundedLabels S seed).card:ℝ)
  let E := ((∏i,M i)^2*(2:ℝ)^Fintype.card ι)/(seed.absNorm:ℝ)
  have hE : 0 ≤ E := by dsimp only [E];positivity
  have hA : 0 ≤ A := Nat.cast_nonneg _
  have hB : 0 ≤ Bn := Nat.cast_nonneg _
  have hterm (a : Allocation seed (Finset.univ : Finset (ι⊕Fin 2)))
      (B : MixedFixedSupport.boundedLabels S seed) :
      ‖frozenWeight H B.val*allocationTerm seed Finset.univ B.val a*
        frozenCoefficient B.val (finiteTupleProduct B.val) R ν Wslot P‖^2/
          rawReduction B.val P ≤ E :=
    seed_frozen_cost H R seed hseed a B.val
      (CenteredMomentCommonAllocationSum.allocation_data S seed B.val
        (Finset.mem_filter.mp B.property).1).1 ν Wslot P M hP hν hWnorm hM hW
  have hAc : A^2 ≤ Ca*(seed.absNorm:ℝ)^(ε/2) :=
    hacount (le_refl (Fintype.card (ι⊕Fin 2))) seed hseed.ne_zero
  have hBc : Bn^2 ≤ Cb*(seed.absNorm:ℝ)^(ε/2) := hbcount S seed hseed.ne_zero
  have hNp : 0<(seed.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hseed.ne_zero)
  calc
    _ ≤ (A*Bn)*(∑_a : Allocation seed (Finset.univ : Finset (ι⊕Fin 2)),
        ∑_B : MixedFixedSupport.boundedLabels S seed,E) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hB)
      exact Finset.sum_le_sum (fun a _=>Finset.sum_le_sum (fun B _=>hterm a B))
    _=A^2*Bn^2*E := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
      dsimp only [A,Bn]
      ring
    _ ≤ (Ca*(seed.absNorm:ℝ)^(ε/2))*(Cb*(seed.absNorm:ℝ)^(ε/2))*E :=
      mul_le_mul_of_nonneg_right (mul_le_mul hAc hBc (sq_nonneg _)
        (mul_nonneg hCa.le (Real.rpow_nonneg hNp.le _))) hE
    _=(Ca*Cb)*(seed.absNorm:ℝ)^ε*((∏i,M i)^2*(2:ℝ)^Fintype.card ι)/(seed.absNorm:ℝ) := by
      have he : (seed.absNorm:ℝ)^(ε/2)*(seed.absNorm:ℝ)^(ε/2)=(seed.absNorm:ℝ)^ε := by
        rw [←Real.rpow_add hNp]
        congr 1
        ring
      dsimp only [E]
      calc
        _=(Ca*Cb)*((seed.absNorm:ℝ)^(ε/2)*(seed.absNorm:ℝ)^(ε/2))*
            ((∏i,M i)^2*(2:ℝ)^Fintype.card ι)/(seed.absNorm:ℝ) := by ring
        _=_ := by rw [he]

end
end Candidate.FourthPower.MixedFirstReferenceChoice
