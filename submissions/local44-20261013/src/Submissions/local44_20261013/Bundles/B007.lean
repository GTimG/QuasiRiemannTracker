/- Deterministically bundled proof sources; original notices are retained below. -/
import Submissions.local44_20261013.Bundles.B000
import Submissions.local44_20261013.Bundles.B001
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.CanonicalErrorPaid
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.OriginalSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowDirect
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceLowReflectionError
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceAllocatedInput
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceInputZeroUniform

/- BEGIN ORIGINAL MODULE Analytic.JointCommonErrorEnergy ; sha256 2cf4c59ee7e6c3fa5f0ec61e21d43e4b21751240c91e1d6a31b06353cb825866 -/
section




/-! Cauchy and the literal source volume are paid only for the extracted
amplification errors. No allocation is applied to the main Gaussian energy. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstSectors CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentGaussEnergy CenteredMomentGaussNormalization
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationEnergy
open CenteredMomentCommonRawScale CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentSecondHeightFamily CenteredMomentOriginalChildEnergy
open CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance commonErrorEnergyDecEq : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma amplificationError_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (v : α → ℕ)
    (p : O) (k : ℕ) (h : O) (q : ℂ) :
    amplificationError S a ha (fun i => q*c i) v p k h =
      q*amplificationError S a ha c v p k h := by
  simp only [amplificationError,Finset.mul_sum,mul_assoc,mul_ite,mul_zero]

lemma errorEnergy_const_mul {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (h p : O) (q : ℂ) :
    errorEnergy S a ha (fun i => q*c i) h p = ‖q‖^2*errorEnergy S a ha c h p := by
  simp only [errorEnergy,amplificationError_const_mul,norm_mul,mul_pow]
  ring

lemma original_errorEnergy_normalized (D : OriginalData ι) (τ : Character)
    (t T : ℝ) (hT : 0 < T) (h p : O) :
    errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
      (fun I => D.beta I*heightCoeff τ t I) h p / T =
    errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
      (D.coefficient τ fixedBadMask t T) h p := by
  have hc : D.coefficient τ fixedBadMask t T =
      fun I : supportedColumns D.columns => (Real.sqrt T:ℂ)⁻¹*(D.beta I*heightCoeff τ t I) := by
    funext I
    rw [heightCoeff_eq_fixed_rowWeight τ t I (Finset.mem_filter.mp I.property).2]
    rfl
  rw [hc,errorEnergy_const_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),inv_pow,Real.sq_sqrt hT.le]
  ring

/-- Pointwise Cauchy for the true three amplification errors. -/
theorem common_errorEnergy_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I ∈ D.S i,I ≠ 0) (hp : ∀ i, ∀ I ∈ D.S (Sum.inl i),Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s ∣ C)
    (τ : Character) (t : ℝ) (L : Ideal O) (h p : O) :
    let Q := residualPool C hC.1 D.columns
    errorEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q =>
        (if IsCoprime C (I : Ideal O) ∧ L ∣ (I : Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I) h p ≤
      ((actualAllocations D.S C).card:ℝ)*∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2*
          errorEnergy Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported (allocatedData D C L B).columns)
            (fun I => (allocatedData D C L B).beta I*heightCoeff τ t I) h p := by
  dsimp only
  have hk (k : ℕ) := CubicEisenstein.norm_sum_sq_le_card Finset.univ
    (fun B : actualAllocations D.S C =>
      frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
        amplificationError Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (fun I => (allocatedData D C L B).beta I*heightCoeff τ t I)
          (fun I => multiplicity p (sourceGenerator (allocatedData D C L B).columns I)) p k h)
  have he := add_le_add (add_le_add (hk 1) (hk 6)) (hk 7)
  simp only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow] at he
  unfold errorEnergy
  simp only [common_amplificationError_allocation D hS hp C hC hseed τ t L p h]
  convert he using 1
  simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib]

/-- The Cauchy factor has precisely the existing live-allocation budget. -/
theorem common_errorEnergy_allocated_inputs (N : ℕ) (a b : ℝ) (ha : 0 < a)
    (s : Input ι) (hcard : Fintype.card ι ≤ N) (haS : a ≤ s.lower) (hbS : s.upper ≤ b)
    (C R seed : Ideal O) (hC : Supported C) (hseed : seed ∣ C)
    (τ : Character) (t : ℝ) (L : Ideal O) (h p : O) :
    let D := original s R seed
    let Q := residualPool C hC.1 D.columns
    errorEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q =>
        (if IsCoprime C (I : Ideal O) ∧ L ∣ (I : Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I) h p /
        volume s ≤
      ((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ))*
        ∑ B : actualAllocations s.pools C,
          if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
            (frozenControl B.val s.M)^2*
              errorEnergy Finset.univ
                (sourceGenerator (original (child s C R B τ t) (R*C) L).columns)
                (sourceGenerator_supported (original (child s C R B τ t) (R*C) L).columns)
                ((original (child s C R B τ t) (R*C) L).coefficient τ fixedBadMask t
                  (volume (child s C R B τ t))) h p
          else 0 := by
  dsimp only
  have hv := volume_pos s
  have hc := CenteredMomentFirstScale.norm_pos C hC.1
  have he := div_le_div_of_nonneg_right
    (common_errorEnergy_allocation (original s R seed) s.pools_ne s.prime C hC hseed τ t L h p) hv.le
  apply he.trans
  rw [mul_div_assoc,Finset.sum_div]
  calc
    _ ≤ ((actualAllocations s.pools C).card:ℝ)*∑ B : actualAllocations s.pools C,
        ((max 1 b)^N/(C.absNorm:ℝ))*
          (if frozenCoefficient B.val C R s.ν s.W s.P ≠ 0 then
            (frozenControl B.val s.M)^2*
              errorEnergy Finset.univ
                (sourceGenerator (original (child s C R B τ t) (R*C) L).columns)
                (sourceGenerator_supported (original (child s C R B τ t) (R*C) L).columns)
                ((original (child s C R B τ t) (R*C) L).coefficient τ fixedBadMask t
                  (volume (child s C R B τ t))) h p else 0) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B _
      have heq := allocated_input_columns s C R seed L B τ t
      have hvB := volume_pos (child s C R B τ t)
      have hr := rawReduction_pos B.val
        (allocation_data s.pools C B.val (Finset.mem_filter.mp B.property).1).1 s.P s.P_pos
      have hvol : volume (child s C R B τ t)*rawReduction B.val s.P = volume s := by
        have hh := allocated_rawVolume_mul (original s R seed) C L B one_ne_zero one_ne_zero
        rw [allocated_input_volume s C R seed L B τ t,original_rawVolume] at hh
        exact hh
      change ‖frozenCoefficient B.val C R s.ν s.W s.P‖^2*_/volume s ≤ _
      by_cases hf : frozenCoefficient B.val C R s.ν s.W s.P = 0
      · simp only [hf,norm_zero,zero_pow (by decide : 2≠0),zero_mul,zero_div,ne_eq,not_true_eq_false,ite_false,mul_zero]
        exact le_rfl
      · rw [if_pos hf]
        have hn := frozen_normalized_bound N a b ha (original s R seed) hcard C hC.1 B s.M
          (fun i => zero_le_one.trans (s.M_ge_one i)) s.P_pos s.ν_bound s.W_bound
          (fun i x hx => ⟨haS.trans (s.slot_support i hx).1,(s.slot_support i hx).2.trans hbS⟩)
        rw [heq.1,heq.2,←hvol]
        have heNorm := original_errorEnergy_normalized
          (original (child s C R B τ t) (R*C) L) τ t _ hvB h p
        calc
          _ = (‖frozenCoefficient B.val C R s.ν s.W s.P‖^2/rawReduction B.val s.P)*
              (errorEnergy Finset.univ
                (sourceGenerator (original (child s C R B τ t) (R*C) L).columns)
                (sourceGenerator_supported (original (child s C R B τ t) (R*C) L).columns)
                (fun I => (original (child s C R B τ t) (R*C) L).beta I*heightCoeff τ t I) h p /
                volume (child s C R B τ t)) := by ring
          _ = _ := by rw [heNorm]
          _ ≤ _ := by
            exact (mul_le_mul_of_nonneg_right hn (errorEnergy_nonneg _ _ _ _ _ _)).trans_eq (by ring)
    _ = _ := by rw [←Finset.mul_sum]; ring

#print axioms common_errorEnergy_allocated_inputs
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointCommonErrorEnergy -/

/- BEGIN ORIGINAL MODULE Analytic.JointErrorSource ; sha256 f583dd0c923b1da0df78adba47c212b8bffa835a118347bdc9880ac45133f676 -/
section



/-! Actual errorInput, restored source Matches, the second common
allocation and the complete divisor allocation, with the refined affine
term carried through the canonical reference estimate. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.Local44.Analytic
open HeckeFamily ConcreteTraceCRT
open CenteredMomentEnergyAllocatedChildren CenteredMomentAllocatedNaturalSource
open CenteredMomentAllocatedNaturalRadial CenteredMomentOriginalRadialComparison
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentRetainedProfile
open CenteredMomentRadialEligibleEnergy
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][instα:DecidableEq α]

open CenteredMomentEnergyCanonicalLiveBound CenteredMomentEnergyCanonicalLiveCapacity
open CenteredMomentEnergyCanonicalPaidSource CenteredMomentEnergyCanonicalCommonPaid
open CenteredMomentEnergyCanonicalReferencePaid CenteredMomentEnergyBandSubtypeTransport
open CenteredMomentFirstAmplifiedCapacityCommon (ratioPenalty)
open CenteredMomentEnergyAllocatedClipped CenteredMomentEnergyAllocatedHomogeneous
open CenteredMomentEnergyChildState CenteredMomentSecondNonexceptionalChosenBlock
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyAllocatedPaid CenteredMomentEnergyAllocatedProfiles
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedZero
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentCommonRadialData
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonAllocationSum
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentAllocatedRayDictionary QuadraticInitialBound

open CenteredMomentEnergyCanonicalChildBound CenteredMomentSectorLocalization
variable (M:Ideal O)[NeZero M]
local instance jointErrorSourceInstance1 : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

open CenteredMomentEnergyCanonicalUniformReference CenteredMomentEnergyAmplifiedRayDictionary
open CenteredMomentFirstAmplifiedPaidAdmission CenteredMomentFirstAmplifiedCapacityCommon
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondExceptionalFamily CenteredMomentSourceLiveColumn
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical CanonicalQuadraticSieve CompletedGauss
open CanonicalRowCompletion ConcretePrimeRowBridge ActualEisensteinCubic
open CenteredMomentSecondHeightFamily
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale CenteredMomentAmplifiedRetainedRadius

open CenteredMomentEnergyCanonicalMainPaid CenteredMomentEnergyCanonicalNestedReference
open CenteredMomentFirstSecondActiveErrorGates CenteredMomentFirstAnnularInput
open CenteredMomentFirstAmplificationChoice (errorMoving errorRemoval)
open CenteredMomentEnergyActiveChildRestoration

open CenteredMomentEnergyCanonicalErrorPaid

theorem refined_error_child_from_bands (W:ℝ→ℂ)(aslot bslot Mcap Lslot εremove lo hi κ:ℝ)
    (a b Mslot εmask:ℝ)(hMslot:0≤ Mslot)(hεmask:0<εmask)(haPlain:0< a)(L:ℝ)(hL:0≤ L)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(ha:0< aslot)(hWs:Function.support W⊆Set.Icc aslot bslot)
    (hW:ContDiff ℝ ∞ W)(hMcap:0≤ Mcap)(hLs:0≤ Lslot)(hε:0<εremove)
    (hκsmall:(1/6:ℝ)≤κ)(hbeta:(51/100:ℝ)≤ HeckeZeroSupremum.beta)
    (hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃dc:ℕ,∃Cc:ℝ,0< Cc ∧ ∀η₀:Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀θ:α→RayQuotient.Characters M H,∀Z:ℝ,Z₀≤ Z →
    ∀εchild:ℝ,∀Q:Ideal O,Q≤ M → ∀C₀ C₁:ℝ,0≤ C₀ → 0≤ C₁ →
    ZeroAt (internalQ Q η₀) (a/max 1 b) b 2 0 L Mcap εchild Z degree S C₀ →
    PositiveAt (α:=α) M H hH W bslot (a/max 1 b) b 2 0 L Lslot lo hi
      Mcap εchild κ Z η₀ Q degree S C₁ →
    ∀(w σ freq:α→ℝ)(v height mesh:ℝ),0≤ mesh → (∀i,0≤ w i) → (∀i,w i≤ mesh) →
    (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) → 0≤ height → (∀i,|freq i|≤ height) →
    ∀src:Input α,Matches M H hH src η₀ θ w σ freq W bslot Z →
    (∀i,src.hi i≤ bslot) → (∀i,src.M i≤ Mslot) →
    ∀(C D R0:Ideal O),∀_hC:Supported C,∀_hD:Supported D,primeSupport C=primeSupport D →
    ∀(E:Finset (CommonIndex C D))(B:actualAllocations src.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R0 src.ν src.W src.P≠0 →
    τ.modulus=src.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E*activeConductor C D} →
    ∀K sigma delta reserve cost asource:ℝ,0< K → 0≤ sigma → 1≤ cost → 0< asource →
    ∀(prime:O),prime≠0 → ∀k:ℕ,(k=1 ∨ k=6 ∨ k=7) →
    sigma/6≤ Real.logb Z (normValue prime) →
    (∀i,∀I∈(activeInput (child src C R0 B τ t)).slots i,IsCoprime (Ideal.span {prime}) I) →
    ∀Bp:actualAllocations (activeInput (child src C R0 B τ t)).pools ((Ideal.span {prime})^k),
    ∀(υ:Character)(v0:ℝ),
    (υ.modulus.absNorm:ℝ)≤ cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k) →
    ∀input:Input (CenteredMomentCommonProfile.liveIndices Bp.val),
    input=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0 →
    let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
      (Real.logb Z (firstNominalScale C D
        (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
      (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
    ∀(Scols:Finset (Ideal O))(βsource:Ideal O→ℂ)(C₂ D₂:Ideal O),
    ∀hC₂:Supported C₂,∀hD₂:Supported D₂,primeSupport C₂=primeSupport D₂ →
    ∀(U:Finset (CommonIndex C₂ D₂))(Rwindow:ℝ)(rows:Finset O)(Wkernel:𝓢(ℝ,ℂ))(dyad:Fin 4→ℤ),
    (∀I:Ideal O,βsource I≠0 → asource*volume input≤(I.absNorm:ℝ)) →
    physicalBlock υ v0 Scols βsource C₂ D₂ hC₂ hD₂ U Rwindow rows Wkernel Kerror dyad≠0 →
    ∀family:RayFourExpansion.RayCharacter→Character,Family υ C₂ D₂ hC₂ hD₂ U family →
    ∀χ:RayFourExpansion.RayCharacter,
    Real.logb Z (dyadicScale (dyad 1))+Real.logb Z ((family χ).modulus.absNorm:ℝ)≤ Mcap →
    ∀Cpick Rpick:Ideal O,Cpick=C₂ ∨ Cpick=D₂ → Rpick≠0 →
    ∀B₂:actualAllocations input.pools Cpick,
    frozenCoefficient B₂.val Cpick Rpick input.ν input.W input.P≠0 →
    ∀Dalloc:Ideal O,∀alloc:Allocation Dalloc
      (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B₂.val⊕Fin 2)),
    ∀p:Profiles a b,p.profile 0=src.W₁ → p.profile 1=src.W₂ →
    src.X₁≤ Z^L → src.X₂≤ Z^L → src.Y₁≤ Z^L → src.Y₂≤ Z^L →
    ∀Mdecl θclip:ℝ,0≤θclip →
    length Z src.X₁+length Z src.X₂+6*κ*(∑i,w i)≤ Mdecl →
    Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ)≤ Mdecl →
    Real.logb Z (max 1 b*max 1 b)≤2*θclip →
    let δpaid:=Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource
    childEnergy (commonData (withHeight input (family χ) v) Cpick Rpick B₂)
      (canonicalRadial (family χ) (internalQ Q η₀) dyad) Dalloc alloc≤
      Cc*(Ideal.absNorm (Rpick*Cpick).radical:ℝ)^εmask*(C₀+C₁)*
        diagonalControl (canonicalRadial (family χ) (internalQ Q η₀) dyad).profile*
        (p.control T)^2*(1+(|v|+height))^(dc+degree+4*n)*
        envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad*(ratioPenalty dyad)^((1:ℝ)/6)*
        Z^(εchild+εremove+((sigma+errorRemoval prime Z k-errorMoving prime Z k)/6+δpaid/6+θclip/3)+κ*mesh):=by
  cases Subsingleton.elim instα (Classical.decEq α)
  obtain ⟨n,T,dc,Cc,hCc,hbound⟩:=nested_original_subsets_reference_paid (α:=α) M H hH W aslot bslot
    Mcap Lslot εremove lo hi κ a b Mslot εmask hMslot hεmask haPlain L hL degree S
    ha hWs hW hMcap hLs hε hbeta hκ
  refine ⟨n,T,dc,Cc,hCc,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound η₀
  refine ⟨Z₀,hZ₀,?_⟩
  intro θ Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    w σ freq v height mesh hmesh hw hwm hwL hσlo hσhi hheight hfreq src hmatch hhi hMs
    C D R0 hC hD hCD E B τ t hB hmod K sigma delta reserve cost asource hK hsigma hcost hasource
    prime hprime k hk hprimeScale hslot Bp υ v0 hυ input hinput
  dsimp only
  intro Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    family hfamily χ hwidth Cpick Rpick hside hRpick B₂ hB₂ Dalloc alloc p hp₁ hp₂
    hX₁ hX₂ hY₁ hY₂ Mdecl θclip hθclip hcap hMdecl hclip
  subst input
  have hz:1< Z:=hZ₀.trans_le hZ
  have hcost0:0< cost:=zero_lt_one.trans_le hcost
  let input:=errorInput src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let restored:=restoredError src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have heInput:input=activeInput restored:=by
    exact error_source_active src C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  let B₂a:=castAllocation input (activeInput restored) heInput Cpick B₂
  let B₂r:=restoreAllocation restored Cpick B₂a
  let Kerror:=errorCommonRadius Z (Real.logb Z (D.absNorm:ℝ))
    (Real.logb Z (firstNominalScale C D
      (Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=> P.val) E}) K (volume src)))
    (Real.logb Z (C.absNorm:ℝ)) sigma delta reserve prime k
  have hKerror:0< Kerror:=by dsimp [Kerror];unfold errorCommonRadius;positivity
  have hP:∀i,1≤ src.P i:=by
    intro i;rw [hmatch.scale];exact Real.one_le_rpow hz.le (hw i)
  have hcap':length Z src.X₁+length Z src.X₂+6*κ*(∑i,Real.logb Z (src.P i))≤ Mdecl:=by
    simpa only [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne'] using hcap
  obtain ⟨hδ,hpar,hshift⟩:=refined_active_error_admission src τ υ C D R0 hC hD hCD E B t hB
    K Z sigma delta reserve cost asource hK hz hcost0 hasource prime hprime k hk hsigma hprimeScale
    hslot Bp v0 hmod Scols βsource C₂ D₂ hC₂ hD₂ hCD₂ U Rwindow rows Wkernel dyad hlower hphysical
    Cpick Rpick hside B₂ hB₂ κ Mdecl hκsmall hP hcap' hMdecl
  have hm:=restoredError_matches M H hH hmatch C R0 B τ t (Ideal.span {prime}) k Bp υ v0
  have caps₁:=common_raw_caps src C R0 B τ t (Z^L) hX₁ hX₂ hY₁ hY₂
  have caps₂:=common_raw_caps (child src C R0 B τ t) ((Ideal.span {prime})^k) (R0*C)
    (restoreAllocation (child src C R0 B τ t) ((Ideal.span {prime})^k) Bp) υ v0 (Z^L)
    caps₁.1 caps₁.2.1 caps₁.2.2.1 caps₁.2.2.2
  have caps₃:=common_raw_caps restored Cpick Rpick B₂r (family χ) v (Z^L)
    caps₂.1 caps₂.2.1 caps₂.2.2.1 caps₂.2.2.2
  have hτnorm:0<(τ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hqpos:0< cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k):=by positivity
  have hdef:=actual_width_le_reference hfamily v0 Scols βsource Rwindow rows Wkernel Kerror hKerror dyad
    hphysical (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) Z hυ hz χ
  have hn:=actual_dyad_ge_one v0 Scols βsource Rwindow rows Wkernel Kerror dyad hphysical
  have hrem : 0 ≤ (sigma+errorRemoval prime Z k-errorMoving prime Z k)/6 := by
    have hlog : 0 ≤ Real.logb Z (normValue prime) := by linarith
    rcases hk with rfl | rfl | rfl <;>
      simp only [errorRemoval,errorMoving] <;> norm_num <;> linarith
  have hsum:(∑i:CenteredMomentCommonProfile.liveIndices B₂.val,Real.logb Z (input.P i.val))=
      ∑i:CenteredMomentCommonProfile.liveIndices B₂.val,w i.val.val.val:=by
    apply Finset.sum_congr rfl
    intro i hi
    change Real.logb Z (src.P i.val.val.val)=w i.val.val.val
    rw [hmatch.scale,Real.logb_rpow (zero_lt_one.trans hz) hz.ne']
  have hparw:Real.logb Z (volume src)+(6*κ-1)*
      (∑i:CenteredMomentCommonProfile.liveIndices B₂r.val,w i.val.val.val)≤ Mdecl:=by
    rw [hsum] at hpar
    have heSum := (restored_slot_sum restored Cpick B₂a (fun i=> w i.val.val)).trans
      (cast_slot_sum input (activeInput restored) heInput Cpick B₂ (fun i=> w i.val.val))
    exact (congrArg (fun x=> Real.logb Z (volume src)+(6*κ-1)*x) heSum).trans_le hpar
  have hshiftw:
      Real.logb Z ((commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₁*
        (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r).X₂*
        ∏i:CenteredMomentCommonProfile.liveIndices B₂r.val,restored.P i.val)-
      Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)≤
      Real.logb Z (volume src)-Mdecl+6*((sigma+errorRemoval prime Z k-errorMoving prime Z k)/6+0)+
        (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
          sourceReserve src input C D Z delta reserve cost asource)+Real.logb Z (ratioPenalty dyad):=by
    change Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
      (commonData (withHeight restored (family χ) v) Cpick Rpick B₂r))-_≤_
    have hpv:= (restored_preVolume restored Cpick Rpick B₂a (family χ) v).trans
      ((cast_preVolume input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v).trans
        (common_preVolume_height input Cpick Rpick B₂ (family χ) υ v v0))
    calc
      _ = Real.logb Z (CenteredMomentAllocatedChildCapacity.preVolume
          (commonData (withHeight input υ v0) Cpick Rpick B₂)) -
          Real.logb Z (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad) :=
        congrArg (fun x=> Real.logb Z x - Real.logb Z
          (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)) hpv
      _ ≤ _ := by
        dsimp only [input]
        convert hshift using 1 <;> ring
  have hh:=hbound (CenteredMomentCommonProfile.liveIndices B.val)
    (CenteredMomentCommonProfile.liveIndices Bp.val) (fun i=>θ i.val.val)
    Z hZ εchild Q hQM C₀ C₁ hC₀ hC₁ hzero hpos
    (fun i=> w i.val.val) (fun i=>σ i.val.val) (fun i=> freq i.val.val) v height mesh hmesh
    (fun i=> hw i.val.val) (fun i=> hwm i.val.val) (fun i=> hwL i.val.val) (fun i=> hσlo i.val.val)
    (fun i=> hσhi i.val.val) hheight (fun i=> hfreq i.val.val)
  have hh := hh restored hm (fun i=> hhi i.val.val) (fun i=> hMs i.val.val)
  have hh := hh Cpick Rpick B₂r
  let allocA:=castDivisorAllocation input (activeInput restored) heInput Cpick B₂ Dalloc alloc
  let allocR:=restoreDivisorAllocation restored Cpick B₂a Dalloc allocA
  have hh := hh Dalloc allocR hRpick
  have hh := hh (family χ) dyad hn hwidth
  have hh := hh p hp₁ hp₂
  have hh := hh caps₃.1 caps₃.2.1 caps₃.2.2.1 caps₃.2.2.2
  have hh := hh (Real.logb Z (volume src)) Mdecl
    (envelopeRef (cost*(τ.modulus.absNorm:ℝ)*Z^(errorMoving prime Z k)) C₂ D₂ U dyad)
    ((sigma+errorRemoval prime Z k-errorMoving prime Z k)/6) 0
    (Mdecl-(Real.logb Z K+Real.logb Z (src.η.modulus.absNorm:ℝ))+
      sourceReserve src input C D Z delta reserve cost asource)
    0 θclip (envelope_pos _ hqpos _ _ hC₂ _ _)
    hrem le_rfl hδ le_rfl hθclip
  have hh := hh hparw
  have hh := hh hshiftw
  have hh := hh (by linarith only [hdef]) hclip
  have he := (cast_child_energy input (activeInput restored) heInput Cpick Rpick B₂ (family χ) v Dalloc alloc
    (canonicalRadial (family χ) (internalQ Q η₀) dyad)).trans
      (restored_child_energy restored Cpick Rpick B₂a (family χ) v Dalloc allocA
        (canonicalRadial (family χ) (internalQ Q η₀) dyad))
  apply he.trans_le
  simpa only [zero_add,add_zero] using hh

#print axioms refined_error_child_from_bands
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointErrorSource -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstOriginalRemainder ; sha256 df71387423259963c5471cec61737af63b22e0bcd1f1aad76c3371cfa25543a3 -/
section




/-! The original first decomposition at the physical source radius,
including the exact additional-mask transport in the source comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceInputTailUniform CenteredMomentSourceInputZeroUniform
open CenteredMomentEnergyOriginalSource CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentHeckeExpansion
open CenteredMomentSourceRectangleMask ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance firstOriginalRemainderSumDecEq : DecidableEq (ι⊕Fin 2) := Classical.decEq _

lemma original_column_coprime_mask (src : Input ι) (R seed I : Ideal O)
    (h : coefficient src R seed I ≠ 0) : IsCoprime I R := by
  obtain ⟨v,hv,hv0,he⟩ := CenteredMomentSupportedZeroEnergy.finiteColumnCoefficient_witness
    (Fintype.piFinset src.pools)
    (profileCoefficient R src.ν src.W src.P src.W₁ src.W₂ src.X₁ src.X₂ src.Y₁ src.Y₂ 1 1 seed) I h
  rw [←he]
  by_contra hn
  apply hv0
  simp only [profileCoefficient,hn,ite_false,mul_zero,zero_mul]

lemma original_source_weight_mask (src : Input ι) (R seed : Ideal O) (m A z : O) (t : ℝ)
    (hml : goodLambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) :
    coefficient src R seed I*rowWeight src.η m A z t I =
      coefficient src R seed I*rowWeight src.η (m*idealGenerator R) A z t I := by
  by_cases hc : coefficient src R seed I = 0
  · simp only [hc,zero_mul]
  rw [←rowWeight_ideal_mask src.η m A z t hml hm2 R I]
  simp only [original_column_coprime_mask src R seed I hc,ite_true,one_mul]

lemma original_finite_energy_mask (src : Input ι) (R seed : Ideal O)
    (m A : O) (t : ℝ) (hml : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy src.η m A t (finiteColumns (Fintype.piFinset src.pools))
      (coefficient src R seed) Φ K =
    finiteHeckeEnergy src.η (m*idealGenerator R) A t (finiteColumns (Fintype.piFinset src.pools))
      (coefficient src R seed) Φ K := by
  have hsum (z : O) :
      (∑ I ∈ finiteColumns (Fintype.piFinset src.pools),coefficient src R seed I*rowWeight src.η m A z t I) =
      ∑ I ∈ finiteColumns (Fintype.piFinset src.pools),
        coefficient src R seed I*rowWeight src.η (m*idealGenerator R) A z t I := by
    apply Finset.sum_congr rfl
    intro I hI
    exact original_source_weight_mask src R seed m A z t hml hm2 I
  unfold finiteHeckeEnergy
  simp_rw [hsum]

theorem first_original_source_remainder (hi : ι → ℝ) (a b ε ξ saving : ℝ)
    (hhi : ∀ i,0 ≤ hi i) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ Sd St : Finset (ℕ×ℕ), ∃ Cd Ct : ℝ, 0 < Cd ∧ 0 < Ct ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)), src.W₁ = W₁ → src.W₂ = W₂ →
      Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      (∀ i,src.hi i ≤ hi i) → volume src.toData ≤ Z →
      0 < sourceRadius src → sourceRadius src ≤ Z →
    ∀ (m A : O), goodLambda ∣ m → (2:O) ∣ m →
    ∀ (R seed : Ideal O) (Φ : 𝓢(ℝ,ℂ)),
      ‖finiteHeckeEnergy src.η m A src.t (finiteColumns (Fintype.piFinset src.pools))
          (coefficient src R seed) Φ Z-
        CenteredMomentFirstSectorLocalization.retainedEnergy src.η m A src.t
          (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R seed)
          Φ Z (sourceRadius src) Z ξ‖ / volume src.toData ≤
      Cd*(plainControl src W₁ W₂)^2*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(1+ε)+
      Ct*(plainControl src W₁ W₂)^2*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(1-saving) := by
  obtain ⟨Sd,Cd,hCd,hdiag⟩ := first_input_zero_capped hi a b 1 ε hhi ha hb (by norm_num) hε
  obtain ⟨St,Ct,hCt,htail⟩ := first_original_source_tail hi a b ξ saving hhi ha hb hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV hsource₀ hsource m A hml hm2 R seed Φ
  have hz := zero_lt_one.trans hZ.1
  have hd := hdiag Z hZ.1.le src W₁ W₂ he₁ he₂ hs₁ hs₂ hshi (by simpa using hV) m A R seed Φ Z hz.le
  have ht := hZ.2 src W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV hsource₀ hsource m A R seed Φ
  rw [CenteredMomentFirstSectorLocalization.finiteHeckeEnergy_sector_localized
    src.η m A src.t hml hm2 (finiteColumns (Fintype.piFinset src.pools))
    (coefficient src R seed) Φ Z (sourceRadius src) Z ξ hz]
  rw [show ∀ x y z : ℂ,x+y+z-y=x+z by intros; ring]
  have hd' : ‖CenteredMomentFirstLocalization.zeroEnergy src.η m A src.t
      (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R seed) Φ Z‖/volume src.toData ≤
      Cd*(plainControl src W₁ W₂)^2*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(1+ε) := by
    apply hd.trans_eq
    rw [Real.rpow_add hz,Real.rpow_one]
    ring
  exact ((div_le_div_of_nonneg_right (norm_add_le _ _) (volume_pos src).le).trans_eq
    (add_div _ _ _)).trans (add_le_add hd' ht)

/-- The only energy term left beside the retained centered source is the
actual equal-product comparison rectangle, with its original radial keep. -/
theorem positive_first_source_remainder (hi : ι → ℝ) (a b ε ξ saving : ℝ)
    (hhi : ∀ i,0 ≤ hi i) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 < ε) (hξ : 0 < ξ) :
    ∃ Sd St : Finset (ℕ×ℕ), ∃ Cd Ct : ℝ, 0 < Cd ∧ 0 < Ct ∧
    ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ (src : Input ι) (W₁ W₂ : 𝓢(ℝ,ℂ)), src.W₁ = W₁ → src.W₂ = W₂ →
      Function.support (W₁ : ℝ → ℂ) ⊆ Set.Icc a b →
      Function.support (W₂ : ℝ → ℂ) ⊆ Set.Icc a b →
      (∀ i,src.hi i ≤ hi i) → volume src.toData ≤ Z →
      0 < sourceRadius src → sourceRadius src ≤ Z →
    ∀ (R : Ideal O) (r : CenteredMomentRadialEligibleEnergy.Radial), r.scale = Z →
      CenteredMomentInductionEnergy.energy src.η (fixedBadMask*idealGenerator R) 1 src.t
        src.W₁ src.W₂ src.slots src.toData.coefficient src.P src.X₁ src.X₂ r.keep r.profile r.scale ≤
      2*‖CenteredMomentFirstSectorLocalization.retainedEnergy src.η (fixedBadMask*idealGenerator R) 1 src.t
          (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R 1)
          r.profile Z (sourceRadius src) Z ξ‖/volume src.toData+
      2*Cd*(plainControl src W₁ W₂)^2*Sd.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*Z^(1+ε)+
      2*Ct*(plainControl src W₁ W₂)^2*St.sup (schwartzSeminormFamily ℝ ℝ ℂ) r.profile*Z^(1-saving)+
      2*CenteredMomentInductionEnergy.energy src.η (fixedBadMask*idealGenerator R) 1 src.t
        src.W₁ src.W₂ src.slots src.toData.coefficient src.P src.Y₁ src.Y₂ r.keep r.profile r.scale := by
  obtain ⟨Sd,St,Cd,Ct,hCd,hCt,hrem⟩ := first_original_source_remainder hi a b ε ξ saving hhi ha hb hε hξ
  refine ⟨Sd,St,Cd,Ct,hCd,hCt,?_⟩
  filter_upwards [hrem] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro src W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV hsource₀ hsource R r hr
  have hml : goodLambda ∣ fixedBadMask := dvd_mul_right _ _
  have hm2 : (2:O) ∣ fixedBadMask := dvd_mul_left _ _
  have hh := hZ.2 src W₁ W₂ he₁ he₂ hs₁ hs₂ hshi hV hsource₀ hsource
    (fixedBadMask*idealGenerator R) 1 (hml.trans (dvd_mul_right _ _)) (hm2.trans (dvd_mul_right _ _)) R 1 r.profile
  have hc := positive_energy_comparison src R r
  rw [original_finite_energy_mask src R 1 fixedBadMask 1 src.t hml hm2 r.profile r.scale,hr] at hc
  have htri := norm_le_norm_sub_add
    (finiteHeckeEnergy src.η (fixedBadMask*idealGenerator R) 1 src.t
      (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R 1) r.profile Z)
    (CenteredMomentFirstSectorLocalization.retainedEnergy src.η (fixedBadMask*idealGenerator R) 1 src.t
      (finiteColumns (Fintype.piFinset src.pools)) (coefficient src R 1) r.profile Z (sourceRadius src) Z ξ)
  have ht := div_le_div_of_nonneg_right htri (volume_pos src).le
  rw [add_div] at ht
  rw [hr]
  change _ ≤ 2*‖finiteHeckeEnergy _ _ _ _ _ _ _ _‖/volume src.toData+_ at hc
  rw [mul_div_assoc] at hc ⊢
  linarith

#print axioms original_finite_energy_mask
#print axioms first_original_source_remainder
#print axioms positive_first_source_remainder
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstOriginalRemainder -/

/- BEGIN ORIGINAL MODULE Analytic.JointFirstWindow ; sha256 65cb643df483b8247078eaaa052b858d2b28ba8f68e420dd43d59a622a735f8d -/
section



/-! Fourier windows are transferred inside the first-label direct sum.
The input is a sum of actual common energies at a common shifted height,
not a separate supremum for each arithmetic label. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.Local44.Analytic
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstPhysicalSource CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentGaussEnergy CenteredMomentFirstColumns
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentSmooth CenteredMomentConjugateWindow
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

namespace FirstJointLabel

def leftWindowValue (s : FirstJointLabel ι) (t θ X : ℝ) (V : ℝ → ℂ) (z : O) : ℂ :=
  leftWindowChild s.data s.parent (fixedBadMask * idealGenerator s.data.R)
    t s.C s.D s.hC s.E s.leftRay s.projector θ X V z

def rightWindowValue (s : FirstJointLabel ι) (t θ X : ℝ) (V : ℝ → ℂ) (z : O) : ℂ :=
  rightWindowChild s.data s.parent (fixedBadMask * idealGenerator s.data.R)
    t s.C s.D s.hC s.hD s.E s.rightRay s.projector θ X V (-z)

theorem leftValue_eq_gauss (s : FirstJointLabel ι) (t : ℝ) (z : O) :
    s.leftValue t z = gaussPolynomial Finset.univ
      (element s.C s.C s.hC.1 s.data.columns)
      (element_supported s.C s.C s.hC.1 s.data.columns)
      (fun I => (if s.projector ∣ (I : Ideal O) then s.data.beta (s.C*I) else 0) *
        heightCoeff s.pair.left t I) z := by
  unfold leftValue leftChild
  dsimp only
  rw [funext (s.pair.left_column s.data t s.projector)]

theorem rightValue_eq_gauss (s : FirstJointLabel ι) (t : ℝ) (z : O) :
    s.rightValue t z = gaussPolynomial Finset.univ
      (element s.C s.D s.hD.1 s.data.columns)
      (element_supported s.C s.D s.hD.1 s.data.columns)
      (fun I => (if s.projector ∣ (I : Ideal O) then s.data.beta (s.D*I) else 0) *
        heightCoeff s.pair.right t I) (-z) := by
  unfold rightValue rightChild
  dsimp only
  rw [funext (s.pair.right_column s.hD s.data t s.projector)]

theorem left_window_integral (s : FirstJointLabel ι) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    s.leftWindowValue t θ X V z = ∫ w : ℝ,
      columnDensity V hVc hVs w * logPhase (θ-w) (Real.log X) *
        s.leftValue (t+2*Real.pi*(w-θ)) z := by
  unfold leftWindowValue leftWindowChild
  simp_rw [leftValue_eq_gauss, s.pair.left_column]
  simpa only [element_span, element_norm] using
    gauss_column_integral Finset.univ (element s.C s.C s.hC.1 s.data.columns)
      (element_supported s.C s.C s.hC.1 s.data.columns)
      (fun I => if s.projector ∣ (I : Ideal O) then s.data.beta (s.C*I) else 0)
      s.pair.left t θ X hX V hVc hVs z

theorem left_window_integrable (s : FirstJointLabel ι) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ =>
      columnDensity V hVc hVs w * logPhase (θ-w) (Real.log X) *
        s.leftValue (t+2*Real.pi*(w-θ)) z) := by
  simp_rw [leftValue_eq_gauss]
  simpa only [element_span] using
    gauss_column_integrable Finset.univ (element s.C s.C s.hC.1 s.data.columns)
      (element_supported s.C s.C s.hC.1 s.data.columns)
      (fun I => if s.projector ∣ (I : Ideal O) then s.data.beta (s.C*I) else 0)
      s.pair.left t θ X hX V hVc hVs z

theorem right_window_integral (s : FirstJointLabel ι) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    s.rightWindowValue t θ X V z = ∫ w : ℝ,
      columnDensity (fun x => star (V x)) (conjugate_compact V hVc)
        (conjugate_smooth V hVs) w * logPhase (-θ-w) (Real.log X) *
        s.rightValue (t+2*Real.pi*(w-(-θ))) z := by
  unfold rightWindowValue rightWindowChild
  simp_rw [rightValue_eq_gauss, s.pair.right_column s.hD, star_columnPhase]
  simpa only [element_span, element_norm] using
    gauss_column_integral Finset.univ (element s.C s.D s.hD.1 s.data.columns)
      (element_supported s.C s.D s.hD.1 s.data.columns)
      (fun I => if s.projector ∣ (I : Ideal O) then s.data.beta (s.D*I) else 0)
      s.pair.right t (-θ) X hX (fun x => star (V x))
      (conjugate_compact V hVc) (conjugate_smooth V hVs) (-z)

theorem right_window_integrable (s : FirstJointLabel ι) (t θ X : ℝ) (hX : 0 < X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ =>
      columnDensity (fun x => star (V x)) (conjugate_compact V hVc)
        (conjugate_smooth V hVs) w * logPhase (-θ-w) (Real.log X) *
        s.rightValue (t+2*Real.pi*(w-(-θ))) z) := by
  simp_rw [rightValue_eq_gauss]
  simpa only [element_span] using
    gauss_column_integrable Finset.univ (element s.C s.D s.hD.1 s.data.columns)
      (element_supported s.C s.D s.hD.1 s.data.columns)
      (fun I => if s.projector ∣ (I : Ideal O) then s.data.beta (s.D*I) else 0)
      s.pair.right t (-θ) X hX (fun x => star (V x))
      (conjugate_compact V hVc) (conjugate_smooth V hVs) (-z)

end FirstJointLabel

theorem joint_label_row_subtype_sum {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Finset O) (f : Λ → O → ℝ) :
    (∑ q : ↥labels × ↥rows, f q.1 q.2) = ∑ l ∈ labels, ∑ z ∈ rows, f l z := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ l : ↥labels, ∑ z ∈ rows, f l z :=
      Finset.sum_congr rfl (fun l _ => Finset.sum_coe_sort rows (fun z => f l z))
    _ = _ := Finset.sum_coe_sort labels (fun l => ∑ z ∈ rows, f l z)

theorem joint_first_left_window_energy {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
    (t X : Λ → ℝ) (hX : ∀ l ∈ labels, 0 < X l) (θ : ℝ)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows,
      1 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).leftEnergy (t l+2*Real.pi*(w-θ)) (U l) (K l)) ≤
        E*(1+‖w‖)^(2*J)) :
    (∑ l ∈ labels, ∑ z ∈ rows, ‖(s l).leftWindowValue (t l) θ (X l) V z‖^2) ≤
      E*(∫ w : ℝ, (1+‖w‖)^J * ‖columnDensity V hVc hVs w‖)^2 := by
  let φ : (↥labels × ↥rows) → ℝ → ℂ := fun q w =>
    logPhase (θ-w) (Real.log (X q.1)) *
      (s q.1).leftValue (t q.1+2*Real.pi*(w-θ)) q.2
  have hi (q : ↥labels × ↥rows) :
      Integrable (fun w => columnDensity V hVc hVs w * φ q w) := by
    simpa only [φ, mul_assoc] using (s q.1).left_window_integrable
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2
  have he (w : ℝ) : (∑ q : ↥labels × ↥rows, ‖φ q w‖^2) ≤ E*((1+‖w‖)^J)^2 := by
    simp only [φ, norm_mul, logPhase_norm, one_mul, ← pow_mul]
    rw [joint_label_row_subtype_sum labels rows
      (fun l z => ‖(s l).leftValue (t l+2*Real.pi*(w-θ)) z‖^2)]
    apply le_trans (Finset.sum_le_sum (fun l hl =>
      (s l).finite_left_energy (t l+2*Real.pi*(w-θ)) (U l) (K l)
        (hK l hl) rows (hU l hl) (hmajor l hl)))
    simpa only [Nat.mul_comm] using henergy w
  have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
    (fun w => (1+‖w‖)^J) (by intro w; positivity) E hE
    (columnDensity_moments V hVc hVs J) hi he
  have hid (q : ↥labels × ↥rows) :
      (∫ w : ℝ, columnDensity V hVc hVs w * φ q w) =
        (s q.1).leftWindowValue (t q.1) θ (X q.1) V q.2 := by
    simpa only [φ, mul_assoc] using ((s q.1).left_window_integral
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2).symm
  simp_rw [hid] at hh
  rw [joint_label_row_subtype_sum labels rows
    (fun l z => ‖(s l).leftWindowValue (t l) θ (X l) V z‖^2)] at hh
  exact hh

theorem joint_first_right_window_energy {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
    (t X : Λ → ℝ) (hX : ∀ l ∈ labels, 0 < X l) (θ : ℝ)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows,
      1 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (J : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).rightEnergy (t l+2*Real.pi*(w-(-θ))) (U l) (K l)) ≤
        E*(1+‖w‖)^(2*J)) :
    (∑ l ∈ labels, ∑ z ∈ rows, ‖(s l).rightWindowValue (t l) θ (X l) V z‖^2) ≤
      E*(∫ w : ℝ, (1+‖w‖)^J * ‖columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w‖)^2 := by
  let φ : (↥labels × ↥rows) → ℝ → ℂ := fun q w =>
    logPhase (-θ-w) (Real.log (X q.1)) *
      (s q.1).rightValue (t q.1+2*Real.pi*(w-(-θ))) q.2
  have hi (q : ↥labels × ↥rows) :
      Integrable (fun w => columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w * φ q w) := by
    simpa only [φ, mul_assoc] using (s q.1).right_window_integrable
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2
  have he (w : ℝ) : (∑ q : ↥labels × ↥rows, ‖φ q w‖^2) ≤ E*((1+‖w‖)^J)^2 := by
    simp only [φ, norm_mul, logPhase_norm, one_mul, ← pow_mul]
    rw [joint_label_row_subtype_sum labels rows
      (fun l z => ‖(s l).rightValue (t l+2*Real.pi*(w-(-θ))) z‖^2)]
    apply le_trans (Finset.sum_le_sum (fun l hl =>
      (s l).finite_right_energy (t l+2*Real.pi*(w-(-θ))) (U l) (K l)
        (hK l hl) rows (hU l hl) (hmajor l hl)))
    simpa only [Nat.mul_comm] using henergy w
  have hh := finite_weighted_integral_energy (columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs)) φ
    (fun w => (1+‖w‖)^J) (by intro w; positivity) E hE
    (columnDensity_moments (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) J) hi he
  have hid (q : ↥labels × ↥rows) :
      (∫ w : ℝ, columnDensity (fun x => star (V x)) (conjugate_compact V hVc) (conjugate_smooth V hVs) w * φ q w) =
        (s q.1).rightWindowValue (t q.1) θ (X q.1) V q.2 := by
    simpa only [φ, mul_assoc] using ((s q.1).right_window_integral
      (t q.1) θ (X q.1) (hX q.1 q.1.property) V hVc hVs q.2).symm
  simp_rw [hid] at hh
  rw [joint_label_row_subtype_sum labels rows
    (fun l z => ‖(s l).rightWindowValue (t l) θ (X l) V z‖^2)] at hh
  exact hh

def jointColumnMoment (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (J : ℕ) : ℝ :=
  ∫ w : ℝ, (1+‖w‖)^J * ‖columnDensity V hVc hVs w‖

theorem jointColumnMoment_nonneg (V : ℝ → ℂ) (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (J : ℕ) : 0 ≤ jointColumnMoment V hVc hVs J := by
  exact integral_nonneg (fun _ => by positivity)

theorem joint_first_window_abs_bound {Λ : Type*} [DecidableEq Λ]
    (labels : Finset Λ) (rows : Finset O) (s : Λ → FirstJointLabel ι)
    (t₁ t₂ X₁ X₂ : Λ → ℝ)
    (hX₁ : ∀ l ∈ labels, 0 < X₁ l) (hX₂ : ∀ l ∈ labels, 0 < X₂ l) (θ : ℝ)
    (V₁ : ℝ → ℂ) (hV₁c : HasCompactSupport V₁) (hV₁s : ContDiff ℝ ∞ V₁)
    (V₂ : ℝ → ℂ) (hV₂c : HasCompactSupport V₂) (hV₂s : ContDiff ℝ ∞ V₂)
    (U : Λ → 𝓢(ℝ, ℂ)) (K : Λ → ℝ)
    (hK : ∀ l ∈ labels, 0 < K l)
    (hU : ∀ l ∈ labels, ∀ z : O, 0 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (hmajor : ∀ l ∈ labels, ∀ z ∈ rows,
      1 ≤ (U l (‖eisEmbedding z‖^2 / K l)).re)
    (J₁ J₂ : ℕ) (E₁ E₂ : ℝ) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hleft : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).leftEnergy (t₁ l+2*Real.pi*(w-θ)) (U l) (K l)) ≤
        E₁*(1+‖w‖)^(2*J₁))
    (hright : ∀ w : ℝ, (∑ l ∈ labels,
      (s l).rightEnergy (t₂ l+2*Real.pi*(w-(-θ))) (U l) (K l)) ≤
        E₂*(1+‖w‖)^(2*J₂)) :
    (∑ l ∈ labels, ∑ z ∈ rows,
      ‖(s l).leftWindowValue (t₁ l) θ (X₁ l) V₁ z‖ *
      ‖(s l).rightWindowValue (t₂ l) θ (X₂ l) V₂ z‖) ≤
      (Real.sqrt E₁ * jointColumnMoment V₁ hV₁c hV₁s J₁) *
      (Real.sqrt E₂ * jointColumnMoment (fun x => star (V₂ x))
        (conjugate_compact V₂ hV₂c) (conjugate_smooth V₂ hV₂s) J₂) := by
  have hl := joint_first_left_window_energy labels rows s t₁ X₁ hX₁ θ V₁ hV₁c hV₁s
    U K hK hU hmajor J₁ E₁ hE₁ hleft
  have hr := joint_first_right_window_energy labels rows s t₂ X₂ hX₂ θ V₂ hV₂c hV₂s
    U K hK hU hmajor J₂ E₂ hE₂ hright
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (labels ×ˢ rows)
    (fun q => ‖(s q.1).leftWindowValue (t₁ q.1) θ (X₁ q.1) V₁ q.2‖)
    (fun q => ‖(s q.1).rightWindowValue (t₂ q.1) θ (X₂ q.1) V₂ q.2‖)
  simp only [Finset.sum_product] at hc
  apply hc.trans
  have hsl := Real.sqrt_le_sqrt hl
  have hsr := Real.sqrt_le_sqrt hr
  change Real.sqrt _ ≤ Real.sqrt (E₁*(jointColumnMoment V₁ hV₁c hV₁s J₁)^2) at hsl
  change Real.sqrt _ ≤ Real.sqrt (E₂*(jointColumnMoment (fun x => star (V₂ x))
    (conjugate_compact V₂ hV₂c) (conjugate_smooth V₂ hV₂s) J₂)^2) at hsr
  rw [Real.sqrt_mul hE₁, Real.sqrt_sq (jointColumnMoment_nonneg V₁ hV₁c hV₁s J₁)] at hsl
  rw [Real.sqrt_mul hE₂, Real.sqrt_sq (jointColumnMoment_nonneg (fun x => star (V₂ x))
    (conjugate_compact V₂ hV₂c) (conjugate_smooth V₂ hV₂s) J₂)] at hsr
  exact mul_le_mul hsl hsr (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (jointColumnMoment_nonneg V₁ hV₁c hV₁s J₁))

#print axioms joint_first_window_abs_bound
#print axioms joint_first_left_window_energy
#print axioms joint_first_right_window_energy
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointFirstWindow -/

/- BEGIN ORIGINAL MODULE Analytic.JointKernel ; sha256 f007257cd04493d68cb199d3791550bddd53d15bd823866f0bf4d643275ebd96 -/
section


/-! Actual smooth kernels, with the scale parameter allowed to depend on
every joint label. The Fourier bound retains one common frequency. -/
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap
open MeasureTheory
namespace SevenEighths.Local44.Analytic
open CenteredMomentSmooth CenteredMomentCauchy FirstPassCubeLabels FourierBridge

theorem whole_kernel_joint_estimate (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (decay J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {κ : Type*} {α β : κ → Type*}
      (rows : Finset κ) (S : (k : κ) → Finset (α k)) (T : (k : κ) → Finset (β k))
      (c : (k : κ) → α k → ℂ) (d : (k : κ) → β k → ℂ)
      (u : (k : κ) → α k → ℝ) (v : (k : κ) → β k → ℝ)
      (R ρ x : κ → ℝ) (η : κ → ℂ), (∀ k, 0 < R k) →
      (∀ k ∈ rows, ‖η k‖ ≤ 1) →
      (∀ k ∈ rows, ‖V 0 (ρ k)‖ ≤ 1) → (∀ k ∈ rows, ‖V 1 (x k)‖ ≤ 1) →
      ∀ E : ℝ,
      (∀ t : ℝ, (∑ k ∈ rows, ‖leftColumn (S k) (c k) (V 2) (u k) t‖*
        ‖rightColumn (T k) (d k) (V 3) (v k) t‖) ≤ E*(1+‖t‖)^J) →
      ‖∑ k ∈ rows, (((1+R k)^decay : ℝ):ℂ)*η k*
        (∑ i ∈ S k, ∑ j ∈ T k, (c k i*star (d k j))*
          wholeKernel W V (R k) (ρ k) (x k) (u k i) (v k j))‖ ≤ C*E := by
  obtain ⟨C,hC,hsep⟩ := whole_kernel_common_majorant W V M hM hV decay J
  let I : ℝ := ∫ t : ℝ, firstLogDensity J t*(1+‖t‖)^J
  have hI : 0 ≤ I := integral_nonneg (fun t =>
    mul_nonneg (firstLogDensity_nonneg J t) (by positivity))
  refine ⟨C*I,mul_nonneg hC hI,?_⟩
  intro κ α β rows S T c d u v R ρ x η hR hη hV₀ hV₁ E he
  choose b hb hp using fun k => hsep (R k) (hR k)
  let density : κ → ℝ → ℂ := fun k t =>
    (((1+R k)^decay : ℝ):ℂ)*η k*rowPhase V (ρ k) (x k) t*b k t
  let m : ℝ → ℝ := fun t => C*firstLogDensity J t
  have hm (t : ℝ) : 0 ≤ m t := mul_nonneg hC (firstLogDensity_nonneg J t)
  have hmajor (k : κ) (hk : k ∈ rows) (t : ℝ) : ‖density k t‖ ≤ m t := by
    have hrpow : 0 ≤ (1+R k)^decay := pow_nonneg (by linarith [hR k]) _
    have hphase : ‖η k‖*‖rowPhase V (ρ k) (x k) t‖ ≤ 1 := by
      simp only [rowPhase,norm_mul,logPhase_norm,mul_one]
      exact (mul_le_of_le_one_left (by positivity) (hη k hk)).trans
        ((mul_le_of_le_one_left (norm_nonneg _) (hV₀ k hk)).trans (hV₁ k hk))
    calc
      _ = ((1+R k)^decay*‖b k t‖)*(‖η k‖*‖rowPhase V (ρ k) (x k) t‖) := by
        simp only [density,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hrpow]
        ring
      _ ≤ (1+R k)^decay*‖b k t‖ :=
        mul_le_of_le_one_right (mul_nonneg hrpow (norm_nonneg _)) hphase
      _ ≤ m t := hp k t
  have hint (k : κ) (_hk : k ∈ rows) : Integrable (fun t => density k t*
      leftColumn (S k) (c k) (V 2) (u k) t*
      rightColumn (T k) (d k) (V 3) (v k) t) := by
    have hi := paired_columns_integrable (b k) V (ρ k) (x k)
      (S k) (T k) (c k) (d k) (u k) (v k) ((((1+R k)^decay : ℝ):ℂ)*η k)
    convert hi using 1
    funext t
    dsimp only [density]
    ring
  have hmi : Integrable (fun t => m t*(1+‖t‖)^J) := by
    simpa only [m,mul_comm,mul_left_comm,mul_assoc] using
      (firstLogDensity_moment_integrable J).const_mul C
  have hbound := joint_integral_pair_bound rows density
    (fun k t => leftColumn (S k) (c k) (V 2) (u k) t)
    (fun k t => rightColumn (T k) (d k) (V 3) (v k) t)
    m (fun t => (1+‖t‖)^J) hm E hmi hint hmajor he
  have hident (k : κ) : (((1+R k)^decay : ℝ):ℂ)*η k*
      (∑ i ∈ S k, ∑ j ∈ T k, (c k i*star (d k j))*
        wholeKernel W V (R k) (ρ k) (x k) (u k i) (v k j)) =
      ∫ t : ℝ, density k t*leftColumn (S k) (c k) (V 2) (u k) t*
        rightColumn (T k) (d k) (V 3) (v k) t := by
    rw [finite_pair_separation W V (R k) (b k) (hb k), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [density,leftColumn,rightColumn]
    ring
  simp_rw [hident]
  convert hbound using 1
  change C*I*E = E*(∫ t : ℝ, C*firstLogDensity J t*(1+‖t‖)^J)
  simp_rw [mul_assoc C]
  rw [integral_const_mul]
  dsimp only [I]
  ring

#print axioms whole_kernel_joint_estimate
end SevenEighths.Local44.Analytic
end
end OAI
end
/- END ORIGINAL MODULE Analytic.JointKernel -/

/- BEGIN ORIGINAL MODULE Analytic.JointOriginalComparisonDeleted ; sha256 fa816c1a6610242497f63987ef229610dcba99a5c45cfb4be6a99f479e59adfc -/
section




set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.Local44.Analytic
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=> HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance originalComparisonDeletedFinite : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)

theorem local_comparison_deleted_energy
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0< aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0< a)(hlo:a≤1/4)(hhi:1≤ b)(hbΦ:0< bΦ)(hepsilon:0< epsilon)(hxi:0< xi)
    (hxicap:xi≤1/1000)(hBmask:0≤ Bmask)(hL:Mcap+Bmask+xi≤ L)
    (B:ℕ)(hB:2≤ B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0< Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0< C ∧ 0< D ∧
      ∀ᶠ Z:ℝ in atTop,1< Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤ K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤ w i) → (∀i,w i≤ Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤ hi) →
      0≤ height → (∀i,|freq i|≤ height) → κ=3/4 →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤ Mcap → 1≤ s.width → s.width≤101/100 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,1≤ X₁ → 1≤ X₂ → X₁≤ Z^(1/4:ℝ) → X₂≤ Z^(3/5:ℝ) →
      (∑i,w i)≤37/1000 →
      ∀D₁∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀D₂∈(CompletedGauss.primeSupport s.puncture).powerset,
      ∀F:Finset α,
      let β:=fun i I=> heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t I;
      radialEnergy (fun z=> polynomial (naturalCharacter s.character z) false W₁
          (X₁/((∏I∈D₁,I).absNorm:ℝ)) 0 t *
        polynomial (naturalCharacter s.character z) false W₂
          (X₂/((∏I∈D₂,I).absNorm:ℝ)) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i))) (β i) (Z^(w i)))
        (effectiveState s).radial.keep s.radial.profile s.radial.scale ≤
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i)):=by
  obtain ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,href⟩:=reference_from_low_with_error (α:=α) M H hH
    Finset.univ Wslot aslot bslot lo hi haslot hsSlot hcSlot
    a b bΦ epsilon xi saving (Mcap+Bmask) ha hlo hhi hbΦ hepsilon hxi B hB degree S
  refine ⟨n,T,Dchild,hDc,nlong,Slong,C,D,hC,hD,?_⟩
  filter_upwards [href] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro Lslot ε κ η₀ Q K hK hlow θ w σ freq t height hw hwL hσlo hσhi hheight hfreq hκ
    s hQ hs hwidthLo hwidthHi W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hslots D₁ hD₁ D₂ hD₂ F
  subst κ
  dsimp only
  let short:=Real.logb Z X₁-Real.logb Z ((∏I∈D₁,I).absNorm:ℝ)
  let along:=Real.logb Z X₂-Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)
  have hsum:0≤∑i∈F,w i:=Finset.sum_nonneg (fun i _=> hw i)
  have hsumle:(∑i∈F,w i)≤∑i,w i:=Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ F) (fun i _ _=> hw i)
  have hg:=local_comparison_deleted_gates s hZ.1 hBmask Mcap L X₁ X₂ (∑i∈F,w i) xi hs hL
    hwidthLo hwidthHi hxi.le hxicap hX₁ hX₂ hcap₁ hcap₂ (hsumle.trans hslots) D₁ D₂ hD₁ hD₂
  dsimp only at hg
  rw [←hg.1,←hg.2.1]
  have hZpos:0< Z:=zero_lt_one.trans hZ.1
  have hdiag:0≤ diagonalControl s.radial.profile:=by unfold diagonalControl;positivity
  have hLpos:0≤ L:=by linarith [s.width_nonneg]
  have hlog:0≤ Real.log Z:=(Real.log_pos hZ.1).le
  have hprod: (∏i∈F,Z^(w i))≤∏i,Z^(w i):=Finset.prod_le_prod_of_subset_of_one_le₀
    (Finset.subset_univ F) (fun i _=> (Real.rpow_pos_of_pos hZpos _).le)
    (fun i _ _=> Real.one_le_rpow hZ.1.le (hw i))
  rcases hg.2.2.2.2.2.2.2 with hd|hr
  · have hdirect:=direct_child_from_low M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi Mcap ε (3/4) Z
      η₀ Q degree S K hlow hBmask ha F θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
      s hQ hs W₁ W₂ hs₁ hs₂ (Z^short) (Z^along)
      (Real.rpow_pos_of_pos hZpos _) (Real.rpow_pos_of_pos hZpos _)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.1)
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hg.2.2.2.2.1) hd.2 hd.1
    exact hdirect.trans (le_add_of_nonneg_right (by positivity))
  · have hh:=hZ.2 Bmask L Lslot Mcap ε (3/4) η₀ Q K hK hlow hBmask F (Finset.subset_univ F)
      θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hs W₂ W₁ hs₂ hs₁ along short
      hg.2.2.2.2.2.1 hg.2.2.2.2.2.2.1 hg.2.2.2.1 hr.2 hr.1
    dsimp only at hh
    have hswap: (fun z=> polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))) =
      (fun z=> polynomial (naturalCharacter s.character z) false W₂ (Z^along) 0 t *
        polynomial (naturalCharacter s.character z) false W₁ (Z^short) 0 t *
        ∏i∈F,naturalSlot (naturalCharacter s.character z) (primePool M H bslot (Z^(w i)))
          (heightCoefficient (fun I=> idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i))):=by funext z;ring
    rw [hswap]
    apply hh.trans
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    apply add_le_add
    · gcongr
      exact hg.2.2.2.2.2.2.1
    · gcongr
      · exact hZ.1.le
      · exact hg.2.2.1.trans (by linarith)

#print axioms local_comparison_deleted_energy
end SevenEighths.Local44.Analytic

end

end OAI
end
/- END ORIGINAL MODULE Analytic.JointOriginalComparisonDeleted -/
