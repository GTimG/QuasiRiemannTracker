/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B003
import Candidate.Bundles.B020
import Candidate.Bundles.B050
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.ReferenceChild
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.OneReflectionEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PositiveSummability
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.Moments
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowCount
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.PrimeRows.RowPartition

/- BEGIN ORIGINAL Cycle25.Numerator.Imported.NumeratorReflectionData; sha256 719141f1c86207748efa35949eb854274052264308ef34b44f0aa06ac63bd4b0 -/
section
                                              
                                                     
                                                         
                                                                 

/-! A fixed reflection presentation for each actual physical row. The same
combined conductor is used both in coefficient damping and in reflection. -/
noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace Cycle25.Weighted.Numerator
open OAI OAI.SevenEighths HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbeRowRadicalConductor CenteredMomentNaturalPrimitive
open CenteredMomentUniformReflectionApproximation CenteredMomentRetainedWeightedSource
local notation "O" => HeckeFamily.O

structure PhysicalReflectionData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) where
  presentation : Character
  primitive : Character
  phase : ℂ
  element_eq : ∀n:O,elementCoeff (rowCharacter S hS u) n=elementCoeff presentation n
  inverse_eq : ∀J:Ideal O,idealCoeff (rowCharacter S hS u).inverse J=idealCoeff presentation.inverse J
  phase_norm : ‖phase‖=1
  conductor_bound : primitive.modulus.absNorm*(redundantIdeal presentation.modulus primitive.modulus).absNorm≤
    fixedConductorConstant S*(Ideal.span {u.val}:Ideal O).radical.absNorm
  split : ∀(G:𝓢(ℝ,ℂ))(X R:ℝ),0<X→
    HeckeDyadic.polynomial (rowCharacter S hS u) false G X 0 0=
      phase*(retainedSchwartz presentation primitive G X R+discardedSchwartz presentation primitive G X R)

theorem physical_reflection_data_exists (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (hn : (rowCharacter S hS u).residue≠1) : Nonempty (PhysicalReflectionData S hS u) := by
  obtain ⟨τ,ψ,g,he,hi,hnτ,hp,hnp,hg,hτ,hcap,hdef,hsplit⟩ := RowConductor.row_original_split S hS u hn
  exact ⟨⟨τ,ψ,g,he,hi,hg,hcap.trans hτ,hsplit⟩⟩

namespace PhysicalReflectionData
variable {S : Finset (Ideal O)} {hS : ∀P∈S,Prime P} {u : FreeRow}

def combinedConductor (D : PhysicalReflectionData S hS u) : ℝ :=
  (D.primitive.modulus.absNorm:ℝ)*(redundantIdeal D.presentation.modulus D.primitive.modulus).absNorm

theorem combined_pos (D : PhysicalReflectionData S hS u) : 0<D.combinedConductor :=
  RowConductor.reflected_scale_pos D.presentation D.primitive

theorem combined_le_radical (D : PhysicalReflectionData S hS u) :
    D.combinedConductor≤(fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).radical.absNorm := by
  unfold combinedConductor
  exact_mod_cast D.conductor_bound

theorem radical_le_row (u : FreeRow) :
    (Ideal.span {u.val}:Ideal O).radical.absNorm≤(Ideal.span {u.val}:Ideal O).absNorm := by
  letI : Finite (O ⧸ (Ideal.span {u.val}:Ideal O)) := Ring.HasFiniteQuotients.finiteQuotient
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
  exact FiniteConductor.absNorm_le_of_le (show (Ideal.span {u.val}:Ideal O)≤(Ideal.span {u.val}:Ideal O).radical from Ideal.le_radical)

theorem combined_le_row (D : PhysicalReflectionData S hS u) :
    D.combinedConductor≤(fixedConductorConstant S:ℝ)*rowNorm u := by
  exact D.combined_le_radical.trans (mul_le_mul_of_nonneg_left
    (by unfold rowNorm;exact_mod_cast radical_le_row u) (Nat.cast_nonneg _))

theorem redundant_le_combined (D : PhysicalReflectionData S hS u) :
    (Ideal.absNorm (∏P∈sourcePrimes D.presentation D.primitive,P):ℝ)≤D.combinedConductor := by
  have hp : (1:ℝ)≤D.primitive.modulus.absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr D.primitive.modulus_ne_bot)
  exact le_mul_of_one_le_left (by positivity) hp

end PhysicalReflectionData

/-- A coefficient dilation bound gives the exact reflected length without
charging the redundant primes or repeated-prime conductor deficit twice. -/
theorem combined_scale_of_dilation (Cu Ccond Nu N Y U y v : ℝ)
    (hC : 0<Ccond) (hNu : 0<Nu) (hN : 0<N) (hU : 0<U)
    (hNuU : Nu≤U) (hY : Y=U^y)
    (hdilation : max 1 (Cu*N/(Ccond*Nu))≤U^v) :
    Cu≤Ccond*U^(1-y+v)*(Y/N) := by
  have hd := (le_max_right 1 (Cu*N/(Ccond*Nu))).trans hdilation
  have hm : Cu*N≤U^v*(Ccond*Nu) := (div_le_iff₀ (mul_pos hC hNu)).mp hd
  have hmul : Cu*N≤Ccond*U^(1+v) := by
    calc
      _ ≤ U^v*(Ccond*Nu) := hm
      _ ≤ U^v*(Ccond*U) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNuU hC.le) (by positivity)
      _ = _ := by rw [Real.rpow_add hU,Real.rpow_one];ring
  rw [hY,←mul_div_assoc,le_div_iff₀ hN]
  apply hmul.trans_eq
  rw [mul_assoc,←Real.rpow_add hU]
  congr 2
  ring

end Cycle25.Weighted.Numerator
end

/- Adapted without mathematical changes from akashlevy/QuasiRiemannTracker
commit 2fd60c0926b66ea18d7436f5ed55250fd006ab5d (Apache-2.0).
Only module paths and the WeightedQRH namespace are changed. -/

end
/- END ORIGINAL Cycle25.Numerator.Imported.NumeratorReflectionData -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.SourceState; sha256 2244f9fb94cf780737d291bf1872b5bba232f1d1f879a3c59996f0d34e7a9026 -/
section
                                                                     
                                  
                                                                               
namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open UniqueFactorizationMonoid CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {D : Cycle25.Weighted.MomentData}

def weighted_sourceFixedIdeal (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma weighted_sourceFixedIdeal_ne_zero (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma weighted_sourceFixedIdeal_ne_top (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus ≤ Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : weighted_sourceFixedIdeal F ≤ Ideal.span {goodLambda})))

lemma weighted_sourceFixedIdeal_le_modulus (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ F.modulus := inf_le_left
lemma weighted_sourceFixedIdeal_le_72 (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) : weighted_sourceFixedIdeal F ≤ Ideal.span {(72:O)} := inf_le_right

def weighted_sourceExceptional (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (weighted_sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

def weighted_sourceExceptionalBound (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (weighted_sourceFixedIdeal F) η)).toFinset

lemma weighted_source_exceptional_norm (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (η : Character)
    (u : FreeRow) (hu : weighted_sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm ≤ weighted_sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (weighted_sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

lemma weighted_source_keep_iff (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val↔¬weighted_sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma weighted_source_fixed_gates (F:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η:Character):
    internalQ (weighted_sourceFixedIdeal F) η≠0 ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ F.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ η.modulus ∧
    internalQ (weighted_sourceFixedIdeal F) η ≤ Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (weighted_sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (weighted_sourceFixedIdeal_le_72 F)⟩

end SevenEighths.Cycle25WeightedNumeratorPhysical

end

end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.SourceState -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.PhysicalMoment; sha256 dad4ece50f86fd832a4a026b30d76a6a14cac659ece3a14450fbf93a31304dd0 -/
section
                                          
                                                    
                                                              
                                                                     

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentRetainedEnergy CenteredMomentPositiveSummability CenteredMomentInductionEnergy
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily ConcreteTraceCRT CenteredMomentRowNorm ActualEisensteinCubic
local notation "O" => HeckeFamily.O

/-- The physical numerator and the source moment character have identical coefficients,
including all natural zero extensions. -/
theorem numerator_polynomial_eq_moment (S : Finset (Ideal O))
    (hS : ∀P∈S, Prime P) (hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
    (u : FreeRow) (W : ℝ → ℂ) (X σ t : ℝ) :
    polynomial (rowCharacter S hS u) false W X σ t =
      polynomial ((momentData (fixedSourcePrincipal S hS)).character (momentElement u))
        false W X σ t := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro I
  simp only [summand,coefficient,Bool.false_eq_true,ite_false,
    numerator_moment_coeff S hS hbad u I.val]

lemma twistProfile_zero_zero (W : ℝ → ℂ) : twistProfile W 0 0 = W := by
  funext x
  simp [twistProfile,HeckeDyadic.shift]

/-- Arbitrary two profiles and scales, rather than only detector witness profiles. -/
theorem actual_pair_source_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (η : Character) (u : FreeRow) (W₁ W₂ : ℝ → ℂ)
    (slots : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hP : ∀i, 0 < P i) :
    positiveSlotRow η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 u.val
      W₁ W₂ slots β P 0 X₁ X₂ =
      polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
        ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i) := by
  rw [natural_unit_mask_positive (naturalRow η u.val u.property.1)]
  rw [←rowMaskElement_eq_fixed]
  have he := positiveSlotRow_eq_product η ((momentData η).character (momentElement u))
    rowMaskElement 1 u.val
    (by simpa only [momentData,momentElement,one_mul] using
      (momentData η).character_spec (momentElement u))
    W₁ W₂ slots β P X₁ X₂ 0 0 hX₁ hX₂ hP
  simpa only [twistProfile_zero_zero] using he

/-- Restricting the actual nonnegative radial energy to a finite physical row set. -/
theorem finite_actual_pair_le_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rows : Finset FreeRow) (η : Character) (Q : Ideal O)
    (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ : ℝ) (hU : 1 ≤ U) (hδ : 0 ≤ δ)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η Q u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (slots : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀i, 0 < P i) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
        ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i)‖^2)
      ≤ energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
        slots β P X₁ X₂ (initialKeep η Q) Φ U := by
  let m := fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)
  let f (z : O) : ℝ := if initialKeep η Q z then
    ‖positiveSlotRow η m 1 z W₁ W₂ slots β P 0 X₁ X₂‖^2*
      (Φ (‖eisEmbedding z‖^2/U)).re else 0
  have hUp : 0 < U := zero_lt_one.trans_le hU
  obtain ⟨B,hB⟩ := product_bounded η m 1 0
    (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹ W₁ W₂ b₁ b₂ X₁ X₂
    hs₁ hs₂ hX₁ hX₂ slots β
  have hsum : Summable f :=
    bounded_radial_summable _ B hB (initialKeep η Q) Φ U hUp
  have hf0 (z : O) : 0 ≤ f z := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (hp _)
    · exact le_rfl
  have he (u : FreeRow) (hu : u ∈ rows) :
      f u.val = ‖polynomial ((momentData η).character (momentElement u)) false W₁ X₁ 0 0 *
        polynomial ((momentData η).character (momentElement u)) false W₂ X₂ 0 0 *
          ∏i, normalizedSlot η rowMaskElement 1 u.val (slots i) (β i) 0 (P i)‖^2 := by
    have hx : ‖eisEmbedding u.val‖^2/U ∈ Set.Icc (0:ℝ) 1 := by
      refine ⟨div_nonneg (sq_nonneg _) hUp.le,(div_le_one hUp).mpr ?_⟩
      rw [eisEmbedding_norm_sq_eq_absNorm_span]
      exact hrows u hu
    dsimp [f]
    rw [if_pos (hkeep u hu),hone _ hx,Complex.one_re,mul_one]
    rw [actual_pair_source_identity η u W₁ W₂ slots β P X₁ X₂ hX₁ hX₂ hP]
  calc
    _ = ∑u∈rows, f u.val := Finset.sum_congr rfl (fun u hu => (he u hu).symm)
    _ = ∑z∈rows.image Subtype.val, f z := by
      rw [Finset.sum_image (fun x _ y _ hxy => Subtype.val_injective hxy)]
    _ ≤ ∑'z, f z := Summable.sum_le_tsum _ (fun z _ => hf0 z) hsum
    _ = _ := rfl

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.PhysicalMoment -/

/- BEGIN ORIGINAL Cycle25.Energy.Physical.PhysicalMomentInput; sha256 05c498a791d60edfd5f600e2fa16c51d0012345aaca2d48de6cbe2bc53620170 -/
section
                                             
                              
                                                        
                                                              
                                                                     

namespace OAI
noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter
namespace SevenEighths.Cycle25WeightedNumeratorPhysical
open HeckeFamily HeckeDyadic HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CenteredMomentDetectorDictionary CenteredMomentNaturalFixedRaySource
open CenteredMomentHeckeSlots CenteredMomentInductionEnergy CenteredMomentEnergyBands
open CenteredMomentDetectorEnergyInitialState CenteredMomentEnergyState
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondHeightFamily
open CenteredMomentRowNorm HeckePrimeAnnular
open CenteredMomentWholeSlotDeletion CenteredMomentRetainedEnergy QuadraticInitialBound
open CenteredMomentPrimeSlot
set_option maxHeartbeats 800000
local notation "O" => HeckeFamily.O

theorem weighted_physical_annular_all {D : Cycle25.Weighted.MomentData} (S:Cycle25ProbeFinalAssembly.WeightedSourceData D)(η₀:Character)
    (P:ℝ)(hP:0<P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=>conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

/-- The certified positive endpoint applied directly to arbitrary physical numerator
profiles. The dependence on the two profiles remains their source seminorm control;
no bound on their Fourier frequencies is assumed here. -/
theorem finite_physical_pair_positiveAt {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (rows : Finset FreeRow)
    (η : Character) (Φ : 𝓢(ℝ,ℂ)) (U bΦ δ mesh ε κ : ℝ)
    (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδtop : δ ≤ 1)
    (hs : Function.support (Φ:ℝ→ℂ) ⊆ Set.Iic bΦ) (hp : ∀x, 0 ≤ (Φ x).re)
    (hη : (η.modulus.absNorm:ℝ) ≤ U^δ)
    (hrows : ∀u∈rows, rowNorm u ≤ U)
    (hkeep : ∀u∈rows, initialKeep η (internalQ (weighted_sourceFixedIdeal F) η) u.val)
    (hone : ∀x∈Set.Icc (0:ℝ) 1, Φ x = 1)
    (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ)
    (hpositive : PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 ε κ
      U η (weighted_sourceFixedIdeal F) degree control C)
    (T : Finset (Fin D.N)) (width : T → ℝ) (z : T → ℂ) (height : ℝ)
    (hw : ∀i, 0 ≤ width i) (hwmax : ∀i, width i ≤ mesh)
    (hz : ∀i, (z i).re = 17/50) (hh : 0 ≤ height) (hzim : ∀i, |(z i).im| ≤ height)
    (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hX₁max : X₁ ≤ U) (hX₂max : X₂ ≤ U)
    (hcap : length U X₁+length U X₂+6*κ*(∑i,width i) ≤ 1+δ) :
    (∑u∈rows, ‖polynomial ((momentData η).character (momentElement u)) false
        (p.profile 0) X₁ 0 0 *
      polynomial ((momentData η).character (momentElement u)) false (p.profile 1) X₂ 0 0 *
      ∏i, normalizedSlot η rowMaskElement 1 u.val (primePool F.modulus ⊤ 2 (U^(width i)))
        (physicalSlotCoefficient η F.W (U^(width i)) (z i)) 0 (U^(width i))‖^2)
      ≤ C*diagonalControl Φ*(p.control control)^2*(1+height)^degree*U^(1+δ+ε) := by
  let state := initialState η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ bΦ U δ hU hδ hs hp hη
  have hwidth : state.width ≤ 2 := by
    change 1+δ ≤ 2
    linarith
  have hX₁' : X₁ ≤ U^(1:ℝ) := by simpa using hX₁max
  have hX₂' : X₂ ≤ U^(1:ℝ) := by simpa using hX₂max
  have hpos := hpositive T (fun _=>1) width (fun _=>33/50) (fun i=>-(z i).im)
    0 height hw hwmax (fun _=>le_rfl) (fun _=>le_rfl) hh
    (fun i=>by simpa only [abs_neg] using hzim i) state rfl hwidth p X₁ X₂
    hX₁ hX₂ hX₁' hX₂' hcap
  have he := finite_actual_pair_le_energy rows η (internalQ (weighted_sourceFixedIdeal F) η)
    Φ U bΦ δ hU hδ hs hp hη hrows hkeep hone (p.profile 0) (p.profile 1)
    (9/4) (9/4) X₁ X₂
    (fun _ hx=>(p.support 0 hx).2) (fun _ hx=>(p.support 1 hx).2) hX₁ hX₂
    (fun i=>primePool F.modulus ⊤ 2 (U^(width i)))
    (fun i=>physicalSlotCoefficient η F.W (U^(width i)) (z i))
    (fun i=>U^(width i)) (fun _=>Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _)
  have hcoef : (fun (i:T) I=>physicalSlotCoefficient η F.W (U^(width i)) (z i) I) =
      (fun (i:T) I=>idealCoeff η.inverse I*HeckePrimeAnnular.annularWeight
        (fun x=>conj (F.W x)) (U^(width i)) (33/50) (-(z i).im) I) := by
    funext i I
    rw [weighted_physical_annular_all F η _ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hU) _) (z i) I,hz i]
    norm_num
  rw [hcoef] at he
  have heq := CenteredMomentDetectorPlainRelativeClass.energy_eq F.modulus ⊤ le_top
    η η (fun (_:T)=>1) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1
    (p.profile 0) (p.profile 1) (fun _=>2) (fun i=>U^(width i))
    (fun i I=>HeckePrimeAnnular.annularWeight (fun x=>conj (F.W x))
      (U^(width i)) (33/50) (-(z i).im) I)
    0 X₁ X₂ (initialKeep η (internalQ (weighted_sourceFixedIdeal F) η)) Φ U
  exact he.trans (heq.le.trans (by simpa [state,initialState,NaturalState.width,NaturalState.mask] using hpos))


/-- Each source prime slot is the conjugate of the actual negative-orientation
canonical amplitude, without deleting any natural ramified zeros. -/
theorem source_physical_slot_conj {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) (u : FreeRow) (P : ℝ) (z : ℂ)
    (hP : 0 < P) :
    normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
      (primePool F.modulus ⊤ 2 P)
      (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W P z) 0 P =
      conj (HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 P z) := by
  apply physical_slot_conj F.modulus ⊤ _ rowMaskElement u.val
    (momentData (fixedSourcePrincipal F.S F.exclusions.prime)).lambda_dvd
    (CenteredMomentDetectorDictionary.source_product_le_rowMask F.S F.exclusions.bad)
    F.W 2 P z hP
  intro I hI _
  exact HeckePrimeRow.identityClass_coprime F.modulus ⊤ (Finset.mem_filter.mp hI).2.2

/-- Conjugating the complete reflected numerator/selected-slot product places
both factors in the positive moment orientation. -/
theorem reflected_pair_norm_eq {D : Cycle25.Weighted.MomentData}
    (F : Cycle25ProbeFinalAssembly.WeightedSourceData D) {ι : Type*} [Fintype ι]
    (u : FreeRow) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (P : ι → ℝ) (hP : ∀i, 0 < P i) (z : ι → ℂ) :
    ‖polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (fun x=>conj (W₁ x)) X₁ 0 0 *
      polynomial (rowCharacter F.S F.exclusions.prime u).inverse false
        (fun x=>conj (W₂ x)) X₂ 0 0 *
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude F.modulus ⊤ u.val F.W 2 (P i) (z i)‖ =
    ‖polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
        (momentElement u)) false W₁ X₁ 0 0 *
      polynomial ((momentData (fixedSourcePrincipal F.S F.exclusions.prime)).character
        (momentElement u)) false W₂ X₂ 0 0 *
      ∏i,normalizedSlot (fixedSourcePrincipal F.S F.exclusions.prime) rowMaskElement 1 u.val
        (primePool F.modulus ⊤ 2 (P i))
        (physicalSlotCoefficient (fixedSourcePrincipal F.S F.exclusions.prime) F.W (P i) (z i))
        0 (P i)‖ := by
  simp_rw [source_physical_slot_conj F u _ _ (hP _)]
  rw [CenteredMomentOneReflectionEnergy.polynomial_inverse_plain _ _ X₁ hX₁,
    CenteredMomentOneReflectionEnergy.polynomial_inverse_plain _ _ X₂ hX₂]
  simp only [Complex.conj_conj]
  rw [numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad,
    numerator_polynomial_eq_moment F.S F.exclusions.prime F.exclusions.bad]
  rw [←Complex.norm_conj (_*_*∏i,_)]
  simp only [map_mul,map_prod,Complex.conj_conj]

end SevenEighths.Cycle25WeightedNumeratorPhysical
end
end OAI

/- Adapted from akashlevy/QuasiRiemannTracker 2fd60c0926b66ea18d7436f5ed55250fd006ab5d, Apache-2.0.
Cycle25 uses the common-mesh variable-kappa positive endpoint and unconditional zero endpoint. -/

end
/- END ORIGINAL Cycle25.Energy.Physical.PhysicalMomentInput -/
