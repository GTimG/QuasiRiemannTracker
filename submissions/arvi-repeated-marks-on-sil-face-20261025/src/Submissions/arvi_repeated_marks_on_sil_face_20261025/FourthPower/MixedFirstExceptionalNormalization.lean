/- Copyright (c) 2026 Sil. Apache-2.0.
The actual extracted exceptional shape, and its first nominal reference.
This file contains numerical identities and consequences of the actual
retained-frequency gate. No row, energy or count estimate is assumed.
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedInnerExceptionalLedger
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstNonexceptionalAllocation
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstReferencePair
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.MixedFirstLiveSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalizationActual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedFirstExceptionalNormalization
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentCommonRawCost
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentAllocationCost CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstMixedAllowance CenteredMomentFirstMixedNormalizationActual
open CenteredMomentFirstMixedRoot CenteredMomentFirstPhysicalSource
open CenteredMomentFirstNonexceptionalPrefactor
open CenteredMomentFirstExceptionalPrefactor
open CenteredMomentFirstScale CenteredMomentFirstPhysicalLedger
open CenteredMomentDescentLedger CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentRankinRadical CenteredMomentCompleteCommon
open CenteredMomentSecondHeightFamily
open QRH.Record1252270103KernelMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalBudget MixedPrincipalCentered MixedPrincipalMasked
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedCommonCoefficient MixedCommonRestriction MixedCommonEnergy
open MixedLiveNormalization MixedFirstNonexceptionalAllocation MixedFirstLiveSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq (κ⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The raw exceptional geometric factor, BEFORE division by source
volume. Its only outside fourth-power gain has already been included. -/
def shape (V p H L K W : ℝ) : ℝ :=
  (V/p)^(4/3:ℝ)*K^(5/6:ℝ)*W^(7/3:ℝ)*(L/H)^(-2/3:ℝ)

theorem raw_prefix_identity (V p a : ℝ) (hV : 0<V) (hp : 0<p) (ha : 0<a) :
    V/p^2*V^(1/3:ℝ)*(a^2/p)^(-2/3:ℝ)=a^(-4/3:ℝ)*(V/p)^(4/3:ℝ) := by
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi]; positivity
  · simp only [Set.mem_Ioi]; positivity
  · simp (disch := positivity) only [Real.log_mul,Real.log_div,Real.log_pow,Real.log_rpow]
    ring

/-- This is precisely the checked savedBudget, restored to raw energy.
Fixed inducing modulus, profiles and the original prefix all remain. -/
theorem source_raw_budget (s : Source ι a b) (ha : 0<a) (J : ℕ)
    (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε K W : ℝ) :
    sourceVolume s*savedBudget s J control Q Z ε K W=
      fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ)*
        shape (sourceVolume s) (pairNorm s.d) (prefixNormMax s.d) s.L K W := by
  have he := raw_prefix_identity (sourceVolume s) (pairNorm s.d) a
    (sourceVolume_pos s) (pairNorm_pos s.hd.1 s.hd.2) ha
  unfold savedBudget sourcePrefactor shape
  calc
    _=fixedQCost Q*(sourceProfile s J control Z ε)^2*(16:ℝ)^(5/6:ℝ)*
      (sourceVolume s/(pairNorm s.d)^2*(sourceVolume s)^(1/3:ℝ)*
        (a^2/pairNorm s.d)^(-2/3:ℝ))*K^(5/6:ℝ)*W^(7/3:ℝ)*
          (s.L/prefixNormMax s.d)^(-2/3:ℝ) := by ring
    _=_ := by rw [he]; ring

/-- Literal frozen supplier, live marked volume and shortened ordinary
prefix. This is not an arbitrary residual vector. -/
def allocationShape (s : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools s) G) (K W : ℝ) : ℝ :=
  ‖frozenWeight (punctureProduct s.S s.H) B.val*
      frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2*
    shape (s.T*∏i : liveIndices B.val,s.P i.val)
      (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
      (prefixNormMax (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))) s.L K W

def slotCost (s : Source ι a b) : ℝ :=
  (∏i,s.M i)^2*((2:ℝ)^Fintype.card ι/pairNorm s.d)^(4/3:ℝ)

theorem slotCost_nonneg (s : Source ι a b) : 0≤slotCost s := by
  have := (pairNorm_pos s.hd.1 s.hd.2).le
  unfold slotCost
  positivity

/-- Actual shortening. The complete G enters the raw-scale comparison,
and the shortened ordinary prefix is retained in L/(H*N(G)). -/
theorem actual_allocation_shape (s : Source ι a b) (G : Id)
    (B : actualAllocations (tuplePools s) G) (K W : ℝ) (hK : 0≤K) (hW : 0≤W) :
    allocationShape s G B K W≤slotCost s*
      ((sourceVolume s/(G.absNorm:ℝ))^(4/3:ℝ)*K^(5/6:ℝ)*W^(7/3:ℝ)*
        (s.L/(prefixNormMax s.d*(G.absNorm:ℝ)))^(-2/3:ℝ)) := by
  let hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
  have hprod : finiteTupleProduct B.val=G := (Finset.mem_filter.mp B.property).2
  have hG : G≠0 := by rw [←hprod]; exact Finset.prod_ne_zero_iff.mpr (fun j _=>hB j)
  have hg : 0<(G.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hG)
  have hd := pairNorm_pos s.hd.1 s.hd.2
  have hv := sourceVolume_pos s
  have hH := prefixNormMax_pos s.d s.hd
  have hpre0 := prefixNormMax_pos
    (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))
    ⟨mul_ne_zero s.hd.1 (hB _),mul_ne_zero s.hd.2 (hB _)⟩
  have hr := rawReduction_pos B.val hB s.P (fun i=>zero_lt_one.trans_le (s.hP i))
  have hM : 0≤∏i,s.M i := Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hM i))
  by_cases hc : frozenCoefficient B.val G s.R s.ν s.Wslot s.P=0
  · simp only [allocationShape,hc,mul_zero,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
    exact mul_nonneg (slotCost_nonneg s)
      (mul_nonneg (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (div_nonneg hv.le hg.le) _)
        (Real.rpow_nonneg hK _)) (Real.rpow_nonneg hW _))
        (Real.rpow_nonneg (div_nonneg s.hL.le (mul_nonneg hH.le hg.le)) _))
  · have hnorm := (frozen_scalar_norm_le (punctureProduct s.S s.H) B.val
        (frozenCoefficient B.val G s.R s.ν s.Wslot s.P)).trans
        (frozenCoefficient_norm B.val G s.R s.ν s.Wslot s.P s.M s.hν s.hWnorm s.hM)
    have hraw := (actual_reduction_norm B.val hB G s.R hprod s.ν s.Wslot s.P
      (fun i=>zero_lt_one.trans_le (s.hP i)) 1 2 zero_lt_one s.hW hc).2
    rw [max_eq_right (by norm_num : (1:ℝ)≤2)] at hraw
    have hquot : (sourceVolume s/pairNorm s.d)/rawReduction B.val s.P≤
        (sourceVolume s/(G.absNorm:ℝ))*((2:ℝ)^Fintype.card ι/pairNorm s.d) := by
      have hi : (1:ℝ)/rawReduction B.val s.P≤(2:ℝ)^Fintype.card ι/(G.absNorm:ℝ) := by
        apply (div_le_div_iff₀ hr hg).mpr
        simpa only [one_mul] using hraw
      calc
        _=(sourceVolume s/pairNorm s.d)*(1/rawReduction B.val s.P) := by ring
        _≤(sourceVolume s/pairNorm s.d)*((2:ℝ)^Fintype.card ι/(G.absNorm:ℝ)) :=
          mul_le_mul_of_nonneg_left hi (div_nonneg hv.le hd.le)
        _=_ := by ring
    have hlive := live_volume_ratio B.val hB s.d s.T s.P
      (fun i=>zero_lt_one.trans_le (s.hP i))
    have hvolume : s.T*∏i,s.P i=sourceVolume s := by unfold sourceVolume;rw [s.hpX]
    rw [hvolume] at hlive
    have hpow := Real.rpow_le_rpow (div_nonneg (div_nonneg hv.le hd.le) hr.le)
      hquot (by norm_num : (0:ℝ)≤4/3)
    rw [Real.mul_rpow (div_nonneg hv.le hg.le) (by positivity)] at hpow
    have hprefix := prefix_max_le_product B.val hB s.d s.hd
    rw [hprod] at hprefix
    have hsave : (s.L/prefixNormMax
        (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))^(-2/3:ℝ)≤
        (s.L/(prefixNormMax s.d*(G.absNorm:ℝ)))^(-2/3:ℝ) := by
      apply Real.rpow_le_rpow_of_nonpos (div_pos s.hL (mul_pos hH hg))
      · exact div_le_div_of_nonneg_left s.hL.le hpre0 hprefix
      · norm_num
    have hn2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hsave0 : 0≤(s.L/prefixNormMax
        (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))^(-2/3:ℝ) :=
      Real.rpow_nonneg (div_nonneg s.hL.le hpre0.le) _
    have hleft0 : 0≤(sourceVolume s/pairNorm s.d/rawReduction B.val s.P)^(4/3:ℝ)*
        K^(5/6:ℝ)*W^(7/3:ℝ)*(s.L/prefixNormMax
          (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))^(-2/3:ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg
        (Real.rpow_nonneg (div_nonneg (div_nonneg hv.le hd.le) hr.le) _)
        (Real.rpow_nonneg hK _)) (Real.rpow_nonneg hW _)) hsave0
    unfold allocationShape shape
    rw [hlive]
    calc
      _≤(∏i,s.M i)^2*
        (((sourceVolume s/(G.absNorm:ℝ))^(4/3:ℝ)*
          ((2:ℝ)^Fintype.card ι/pairNorm s.d)^(4/3:ℝ))*K^(5/6:ℝ)*W^(7/3:ℝ)*
            (s.L/(prefixNormMax s.d*(G.absNorm:ℝ)))^(-2/3:ℝ)) := by
        gcongr <;> first | exact hleft0 | exact hsave0
      _=_ := by unfold slotCost;ring

/-- Exact substitution of the sibling's literal extracted Source into
the checked raw savedBudget. This identifies the actual cost to which
actual_allocation_reference applies; all live profile costs remain. -/
theorem allocated_raw_budget (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (G : Id) (B : actualAllocations (tuplePools s) G)
    (J : ℕ) (control : Finset (ℕ×ℕ)) (Q : Id) (Z ε K W : ℝ) :
    ‖frozenWeight (punctureProduct s.S s.H) B.val*
      frozenCoefficient B.val G s.R s.ν s.Wslot s.P‖^2*
      (sourceVolume (allocatedLiveSource s hb cover G B)*
        savedBudget (allocatedLiveSource s hb cover G B) J control Q Z ε K W)=
    (fixedQCost Q*(sourceProfile (allocatedLiveSource s hb cover G B) J control Z ε)^2*
      (16:ℝ)^(5/6:ℝ)*a^(-4/3:ℝ))*allocationShape s G B K W := by
  have hs : shape (sourceVolume (allocatedLiveSource s hb cover G B))
      (pairNorm (allocatedLiveSource s hb cover G B).d)
      (prefixNormMax (allocatedLiveSource s hb cover G B).d)
      (allocatedLiveSource s hb cover G B).L K W=
      shape (s.T*∏i : liveIndices B.val,s.P i.val)
        (pairNorm (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1)))
        (prefixNormMax (s.d.1*B.val (Sum.inr 0),s.d.2*B.val (Sum.inr 1))) s.L K W := by
    dsimp only [allocatedLiveSource,liveSource,allocationSource,sourceVolume,Source.prefixPair]
    rw [s.hpX]
  rw [source_raw_budget (allocatedLiveSource s hb cover G B) ha,hs]
  unfold allocationShape
  ring

/-- No analytic hypothesis: this is the reference denominator used by
the already checked actual_source_reference_pair. -/
def reference (τ : Character) (C D : Id) (V Z : ℝ) : ℝ :=
  (τ.modulus.absNorm:ℝ)*(V/(C.absNorm:ℝ))^2*Z^(allowance C D Z)

def deficit (C D : Id) (E : Finset (CommonIndex C D)) (K V Z : ℝ) (n : ℤ) : ℝ :=
  Real.logb Z (D.absNorm:ℝ)+Real.logb Z
    (firstNominalScale C D (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K V)-
      Real.logb Z (dyadicScale n)

/-- Signed common width completed at its actual positive part. K4 is
handled by W^(7/3), so it is not counted a second time in this scale. -/
def nominalChildScale (C D : Id) (E : Finset (CommonIndex C D))
    (K V Z κ : ℝ) (n : ℤ) : ℝ :=
  Z^(Real.logb Z (dyadicScale n)+max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ)

private theorem scalar_saving (c d D₀ q r B κ δ : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hqr : r≤q)
    (hδ : 0≤δ) (hraw : 3*c-5*d-r≤6*B) (hD : d-δ≤D₀) :
    2*c/3-5*(δ+κ)/6≤firstSaving c D₀ 0 q 0 B (max (D₀-c) 0+κ) 0 := by
  unfold firstSaving
  by_cases h : 0≤D₀-c
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

/-- The first saving is supplied by actual ideals, their exact fixed
character presentation and the retained nominal frequency, not assumed. -/
theorem actual_nominal_saving (η τ : Character) (C D : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z Tsec Csec ξ κ : ℝ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hCsec : 1≤Csec) (hξ : 0≤ξ)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hsec : Tsec≤Csec*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K V)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    2*Real.logb Z (C.absNorm:ℝ)/3-5*(frequencyLoss Z Csec ξ+κ)/6≤
      firstSaving (Real.logb Z (C.absNorm:ℝ)) (deficit C D E K V Z n) 0
        (Real.logb Z (τ.modulus.absNorm:ℝ)) 0 (allowance C D Z)
        (max (deficit C D E K V Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ) 0 := by
  have hc := Real.logb_nonneg hZ (ideal_norm_one_le hC.1)
  have hq := Real.logb_nonneg hZ (ideal_norm_one_le τ.modulus_ne_bot)
  have hη := Real.logb_nonneg hZ (ideal_norm_one_le η.modulus_ne_bot)
  have he := Real.logb_nonneg hZ (ideal_norm_one_le (subsetGenerator_supported C D hC E).1)
  have hfixed : 0≤Real.logb Z fixedPresentationCost := by
    apply Real.logb_nonneg hZ
    have h₁ := ideal_norm_one_le (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero)
    have h₂ : (1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ) :=
      ideal_norm_one_le (by simp)
    unfold fixedPresentationCost
    nlinarith
  have hw := actual_reference_width η τ C D hC E K Z hK hZ hmod
  have hqr : Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)≤
      Real.logb Z (τ.modulus.absNorm:ℝ) := by linarith
  have hraw : 3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)≤6*allowance C D Z := by
    unfold allowance
    linarith [le_max_left (3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
      Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) (0:ℝ)]
  have hdef := retained_deficit C D _ (subsetGenerator_supported C D hC E).1
    Z K V Tsec Csec ξ hZ hK hV (zero_lt_one.trans_le hCsec) hsec n hn
  rw [commonPart_of_equal_support D C hD.1 hCD.symm] at hdef
  exact scalar_saving _ _ _ _ _ _ _ _ hc hq (allowance_nonneg C D Z) hqr
    (frequencyLoss_nonneg Z Csec ξ hZ hCsec hξ) hraw hdef

/-- Exact exceptional ratio. The common shortening is not falsely
replaced by 1/N(C); its logarithm remains until the nominal cancellation. -/
theorem reference_identity (η τ : Character) (C D : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K V Z j g W H L : ℝ)
    (hK : 0<K) (hV : 0<V) (hZ : 1<Z) (hW : 0<W) (hH : 0<H) (hL : 0<L)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D}) :
    ((V/(C.absNorm:ℝ))^(4/3:ℝ)*(Z^(j+g))^(5/6:ℝ)*W^(7/3:ℝ)*
      (L/(H*(C.absNorm:ℝ)))^(-2/3:ℝ))/reference τ C D V Z=
    Z^(Real.logb Z V-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z fixedPresentationCost)/6-
      firstSaving (Real.logb Z (C.absNorm:ℝ))
        (Real.logb Z (D.absNorm:ℝ)+Real.logb Z (firstNominalScale C D
          (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K V)-j)
        0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0 (allowance C D Z) g 0+
      7*Real.logb Z W/3-2*(Real.logb Z L-Real.logb Z H-Real.logb Z (C.absNorm:ℝ))/3) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : 0<(C.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hC.1)
  have he := actual_exceptional_reference η τ C D hC hD hCD E K V Z j g 0 0 0
    hK hV hZ hmod
  dsimp only at he
  simp only [neg_zero,Real.rpow_zero,mul_one,div_one] at he
  have hp : (V/(C.absNorm:ℝ))^(4/3:ℝ)=
      (V/(C.absNorm:ℝ))*(V/(C.absNorm:ℝ))^(1/3:ℝ) := by
    calc
      _=(V/(C.absNorm:ℝ))^((1:ℝ)+1/3) := by norm_num
      _=_ := by rw [Real.rpow_add (div_pos hV hc),Real.rpow_one]
  have hw : W^(7/3:ℝ)=Z^(7*Real.logb Z W/3) := by
    rw [show 7*Real.logb Z W/3=Real.logb Z W*(7/3) by ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' hW]
  have hl : (L/(H*(C.absNorm:ℝ)))^(-2/3:ℝ)=
      Z^(-2*(Real.logb Z L-Real.logb Z H-Real.logb Z (C.absNorm:ℝ))/3) := by
    rw [show -2*(Real.logb Z L-Real.logb Z H-Real.logb Z (C.absNorm:ℝ))/3=
      Real.logb Z (L/(H*(C.absNorm:ℝ)))*(-2/3) by
        rw [Real.logb_div hL.ne' (mul_pos hH hc).ne',Real.logb_mul hH.ne' hc.ne'];ring,
      Real.rpow_mul hz.le,Real.rpow_logb hz hZ.ne' (div_pos hL (mul_pos hH hc))]
  rw [hp]
  calc
    _=((V/(C.absNorm:ℝ))*(V/(C.absNorm:ℝ))^(1/3:ℝ)*(Z^(j+g))^(5/6:ℝ)/
      reference τ C D V Z)*W^(7/3:ℝ)*(L/(H*(C.absNorm:ℝ)))^(-2/3:ℝ) := by ring
    _=_ := by
      rw [reference,he,hw,hl,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1
      ring

/-- At the actual retained first scale, shortening cancels the first
common saving. This bound is uniform in N(C), and preserves 7d/3 exactly.
It is compatible with every cross term of actual_source_reference_pair. -/
theorem retained_reference_bound (s : Source ι a b) (η τ : Character) (C D : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (K Z Tsec Csec ξ κ W : ℝ)
    (hK : 0<K) (hZ : 1<Z) (hW : 0<W) (hCsec : 1≤Csec) (hξ : 0≤ξ)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hsec : Tsec≤Csec*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K (sourceVolume s))
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    ((sourceVolume s/(C.absNorm:ℝ))^(4/3:ℝ)*
      (nominalChildScale C D E K (sourceVolume s) Z κ n)^(5/6:ℝ)*W^(7/3:ℝ)*
      (s.L/(prefixNormMax s.d*(C.absNorm:ℝ)))^(-2/3:ℝ))/
        reference τ C D (sourceVolume s) Z≤
    Z^(Real.logb Z (sourceVolume s)-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z fixedPresentationCost)/6-2*(Real.logb Z s.L-Real.logb Z (prefixNormMax s.d))/3+
      7*Real.logb Z W/3+5*(frequencyLoss Z Csec ξ+κ)/6) := by
  have hs := actual_nominal_saving η τ C D hC hD hCD E K (sourceVolume s) Z Tsec Csec ξ κ
    hK (sourceVolume_pos s) hZ hCsec hξ hmod hsec n hn
  have he := reference_identity η τ C D hC hD hCD E K (sourceVolume s) Z
    (Real.logb Z (dyadicScale n))
    (max (deficit C D E K (sourceVolume s) Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ)
    W (prefixNormMax s.d) s.L hK (sourceVolume_pos s) hZ hW
    (prefixNormMax_pos s.d s.hd) s.hL hmod
  have hscale : nominalChildScale C D E K (sourceVolume s) Z κ n=
      Z^(Real.logb Z (dyadicScale n)+
        (max (deficit C D E K (sourceVolume s) Z n-Real.logb Z (C.absNorm:ℝ)) 0+κ)) := by
    unfold nominalChildScale
    congr 1
    ring
  rw [hscale,he]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  dsimp only [deficit] at hs ⊢
  linarith

/-- The complete literal allocation geometry in the common reference.
Its amplitude is proved from the actual frozen coefficients. -/
theorem actual_allocation_reference (s : Source ι a b) (η τ : Character) (C D : Id)
    (hC : Supported C) (hD : Supported D)
    (hCD : CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (E : Finset (CommonIndex C D)) (B : actualAllocations (tuplePools s) C)
    (K Z Tsec Csec ξ κ W : ℝ) (hK : 0<K) (hZ : 1<Z) (hW : 0<W)
    (hCsec : 1≤Csec) (hξ : 0≤ξ)
    (hmod : τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E*activeConductor C D})
    (hsec : Tsec≤Csec*firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D=>P.val) E}) K (sourceVolume s))
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    allocationShape s C B (nominalChildScale C D E K (sourceVolume s) Z κ n) W/
      reference τ C D (sourceVolume s) Z≤slotCost s*
    Z^(Real.logb Z (sourceVolume s)-5*(Real.logb Z K+Real.logb Z (η.modulus.absNorm:ℝ)+
      Real.logb Z fixedPresentationCost)/6-2*(Real.logb Z s.L-Real.logb Z (prefixNormMax s.d))/3+
      7*Real.logb Z W/3+5*(frequencyLoss Z Csec ξ+κ)/6) := by
  have hchild : 0≤nominalChildScale C D E K (sourceVolume s) Z κ n :=
    Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have href : 0≤reference τ C D (sourceVolume s) Z := by
    unfold reference
    positivity
  have h := div_le_div_of_nonneg_right
    (actual_allocation_shape s C B _ W hchild hW.le) href
  calc
    _≤slotCost s*((sourceVolume s/(C.absNorm:ℝ))^(4/3:ℝ)*
        (nominalChildScale C D E K (sourceVolume s) Z κ n)^(5/6:ℝ)*W^(7/3:ℝ)*
        (s.L/(prefixNormMax s.d*(C.absNorm:ℝ)))^(-2/3:ℝ)/
          reference τ C D (sourceVolume s) Z) := by simpa only [mul_div_assoc] using h
    _≤_ := mul_le_mul_of_nonneg_left
      (retained_reference_bound s η τ C D hC hD hCD E K Z Tsec Csec ξ κ W
        hK hZ hW hCsec hξ hmod hsec n hn) (slotCost_nonneg s)

end
end Candidate.FourthPower.MixedFirstExceptionalNormalization
