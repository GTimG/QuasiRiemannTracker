/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Submissions.cycle61_c0125139.Bundles.B003
import Submissions.cycle61_c0125139.Bundles.B138
import Submissions.cycle61_c0125139.Bundles.B183
import Submissions.cycle61_c0125139.Bundles.B185
import Submissions.cycle61_c0125139.Bundles.B187
import Submissions.cycle61_c0125139.Bundles.B188
import Submissions.cycle61_c0125139.Bundles.B190
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.NaturalRowSourceFamily

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceNaturalRow; sha256 d3a38a740c17a6671d393dcab9e19c2e4d35798d46ec8a15208992e4f7dad7ce -/
section
                                  
                                                                 
                                                                   

set_option autoImplicit false
set_option maxHeartbeats 40000

namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily CenteredMomentNaturalRowSource
open ProbePhysical CenteredMomentDetectorDictionary Cycle25ProbeFinalAssembly
local notation "O" => HeckeFamily.O

private theorem canonical_excluded_one (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1) :
    excluded (Character.ofResidue M hM χ hu) 1 = Character.ofResidue M hM χ hu := by
  have hsupport : CompletedGauss.primeSupport (1 : Ideal O) = ∅ := by
    change UniqueFactorizationMonoid.primeFactors (1 : Ideal O) = ∅
    exact UniqueFactorizationMonoid.primeFactors_one
  unfold excluded Character.excludePrimes
  simp only [hsupport, Finset.prod_empty, mul_one]
  unfold Character.refineModulus
  have hinflate : ResidueCharacter.inflate (show M ≤ M from le_refl M) χ = χ := by
    apply DFunLike.ext
    intro x
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [ResidueCharacter.inflate_mk]
    split_ifs with hn
    · rfl
    · exact (MulChar.map_nonunit χ hn).symm
  change Character.ofResidue M _ (ResidueCharacter.inflate _ χ) _ = _
  congr 1

private theorem fixed_source_supported (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) (n : O)
    (hn : elementCoeff (fixedSourcePrincipal S hS) n ≠ 0) :
    Supported (Ideal.span {n}) := by
  have hunit := MulChar.apply_ne_zero_iff.mp hn
  have hcop : IsCoprime (Ideal.span {n}) (fixedSourcePrincipal S hS).modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp hunit
  have hmod : (fixedSourcePrincipal S hS).modulus ≤ Ideal.span {fixedBadMask} := by
    have h := source_product_le_rowMask S hbad
    simpa only [fixedSourcePrincipal, HeckeRayFamily.character, Character.ofResidue,
      ProbeHighRowFamily.rowMaskElement, fixedBadMask, mul_comm] using h
  have hc : IsCoprime n fixedBadMask :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hcop.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hmod))
  have hlam : IsCoprime goodLambda n := (hc.symm.of_isCoprime_of_dvd_left (dvd_mul_right _ _))
  have htwo : IsCoprime (2 : O) n := (hc.symm.of_isCoprime_of_dvd_left (dvd_mul_left _ _))
  apply (supported_span_iff n).mpr
  refine ⟨PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp hlam, ?_⟩
  have hneg : IsCoprime (-2 : O) n := htwo.of_isCoprime_of_dvd_left ⟨-1, by ring⟩
  simpa only [neg_dvd] using negative_two_prime.irreducible.coprime_iff_not_dvd.mp hneg

/-- The original fixed exclusions absorb the natural row's fixed sixth mask. -/
theorem actual_fixed_source_unit_row (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) (n : O) :
    elementCoeff (fixedSourcePrincipal S hS) n =
      rowTwist (elementHom (fixedSourcePrincipal S hS)) fixedBadMask 1 1 n := by
  by_cases hs : Supported (Ideal.span {n})
  · have hcop : IsCoprime (Ideal.span {n}) (Ideal.span {fixedBadMask}) :=
      (Ideal.isCoprime_span_singleton_iff _ _).mpr (fixedBadMask_coprime n hs).symm
    have hrow := idealRowHom_sixth_mask fixedBadMask (Ideal.span {n}) hs
    rw [ite_eq_left hcop] at hrow
    change elementCoeff _ n = elementCoeff _ n * idealRowHom (fixedBadMask ^ 6 * 1 ^ 4 * 1) _
    simp only [one_pow, mul_one]
    change elementCoeff _ n = elementCoeff _ n * idealRowHom (fixedBadMask ^ 6) (Ideal.span {n})
    rw [hrow, mul_one]
  · have hz : elementCoeff (fixedSourcePrincipal S hS) n = 0 := by
      by_contra h
      exact hs (fixed_source_supported S hS hbad n h)
    change elementCoeff _ n = elementCoeff _ n * idealRowHom _ _
    rw [hz, zero_mul]

def fixedSourceNaturalRow (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (hbad : fixedBadPrimes ⊆ S) : NaturalRow (fixedSourcePrincipal S hS) (1 : O) where
  character := fixedSourcePrincipal S hS
  modulus_bound := by
    have hm : 1 ≤ (Ideal.span {fixedBadMask} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    have h72 : 1 ≤ (Ideal.span {(72 : O)} : Ideal O).absNorm :=
      Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
    simp only [rowConductorBound, Ideal.span_singleton_one, Ideal.absNorm_top, one_pow, mul_one]
    exact (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt hm)).trans
      (Nat.le_mul_of_pos_right _ (Nat.zero_lt_of_lt h72))
  element := actual_fixed_source_unit_row S hS hbad

theorem actual_fixed_source_natural_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (hbad : fixedBadPrimes ⊆ S) :
    fixedSourcePrincipal S hS = excluded (fixedSourceNaturalRow S hS hbad).character 1 := by
  change fixedSourcePrincipal S hS = excluded (fixedSourcePrincipal S hS) 1
  unfold fixedSourcePrincipal HeckeRayFamily.character
  exact (canonical_excluded_one _ _ _ _).symm

theorem actual_weighted_source_natural_excluded {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D) :
    fixedSourcePrincipal F.S F.exclusions.prime =
      excluded (fixedSourceNaturalRow F.S F.exclusions.prime F.exclusions.bad).character 1 :=
  actual_fixed_source_natural_excluded F.S F.exclusions.prime F.exclusions.bad

end
end OAI.SevenEighths.Cycle61InitialMass

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_fixed_source_unit_row
#print axioms OAI.SevenEighths.Cycle61InitialMass.fixedSourceNaturalRow
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_fixed_source_natural_excluded
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_weighted_source_natural_excluded

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceNaturalRow -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceErrorPayment; sha256 317a55fa54fb4c220ba256bacf87108e139648381b87c054120ec4d1d146101e -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                      
                                                             
                                                            
                                                          

set_option autoImplicit false
set_option maxHeartbeats 80000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical ContDiff ComplexConjugate SchwartzMap
open Filter HeckeFamily Cycle25ProbeFinalAssembly Cycle25WeightedNumeratorPhysical
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentDetectorDictionary ProbePhysical
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentLogDyadic

/-- Specialize the normalized-family payment to the exact weighted source.
Its fixed modulus gates are derived internally; only the normalized estimate
remains explicit. -/
theorem actual_weighted_source_error_paid_of_normalized {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(Ψ : 𝓢(ℝ,ℂ)) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    let Qfix:=internalQ (weighted_sourceFixedIdeal F) η
    (∀T : Finset (Fin D.N),∃degree windowDegree dN : ℕ,
      ∃SN : Finset (ℕ×ℕ),∃Cn : ℝ,0≤ Cn ∧ ∀ᶠZ : ℝ in atTop,
        GeometryAffineErrorNormalizedSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T
          degree windowDegree Qfix SN dN Cn Z) →
    ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z := by
  intro W hW hs η Qfix hnormalized
  exact actual_affine_error_uniform_paid_of_normalized (α:=Fin D.N) F.modulus ⊤ le_top
    0 logAnnulus_compact logAnnulus_smooth F.S F.exclusions.bad W hW hs Ψ η η εaffine mesh
    hε hmesh Qfix (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 hnormalized

/-- The original retained error estimate for the exact weighted source,
with the normalized-family estimate and fixed modulus gates supplied. -/
theorem actual_weighted_source_error_paid {D : Cycle25.Weighted.MomentData}
    (F : WeightedSourceData D)(εaffine mesh : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hβ : 51/100≤ HeckeZeroSupremum.beta)(Ψ : 𝓢(ℝ,ℂ)) :
    let W:=fun x=>conj (F.W x)
    let hW : Continuous W:=(Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)).continuous
    let hs : Function.support W⊆Set.Icc (1:ℝ) 2:=by
      intro x hx
      exact F.complex_support (by intro hz;exact hx (by change conj (F.W x)=0;rw [hz];simp))
    let η:=fixedSourcePrincipal F.S F.exclusions.prime
    ∀T : Finset (Fin D.N),∃S : Finset (ℕ×ℕ),∃degree : ℕ,∃C : ℝ,0≤ C ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineErrorPaidSpec F.modulus ⊤ le_top F.S W hW hs Ψ η η mesh εaffine T S degree C Z := by
  intro W hW hs η
  apply actual_weighted_source_error_paid_of_normalized F εaffine mesh hε hmesh Ψ
  have hSmooth : ContDiff ℝ ∞ W:=Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  exact actual_affine_error_normalized_family (α:=Fin D.N) F.modulus ⊤ le_top
    F.S F.exclusions.bad W hSmooth hs hβ Ψ η η (weighted_sourceFixedIdeal F)
    (weighted_sourceFixedIdeal_le_modulus F) (weighted_source_fixed_gates F η).1
    (internalQ_ne_top _ (weighted_sourceFixedIdeal_ne_top F) η)
    (weighted_source_fixed_gates F η).2.2.2 εaffine mesh hε hmesh0 hmesh hmeshμ hmeshcap

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_weighted_source_error_paid_of_normalized
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_weighted_source_error_paid

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometrySourceErrorPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineHighUniform; sha256 f913eb08a6b245b3442cc1e56916eec99657c37059b2a83a5b2d0fd0535fa6f7 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                             
                                                                 

set_option autoImplicit false
set_option maxHeartbeats 60000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical ContDiff
open Filter HeckeFamily CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CanonicalQuadraticSieve ConcretePrimeRowBridge Cycle61Moment
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Select every actual-subset density dictionary before fixing one common
height cutoff. Only the scalar loss rate uses the ambient cardinality.
The exact fiber receipt remains explicit until its separate proof is joined. -/
theorem actual_affine_high_uniform_schedule_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (μ Cs bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/128)(hCs : 1≤ Cs)(hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        GeometryAffineHighScheduleGates W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0< K ∧
        ∀(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤ Z ∧
            GeometryAffineHighSelectedCostSpec (α:=T) M H hH W hbeta P μ δ
              (geometryAffineHighTarget μ δ) (fun _ _ _ _ _=>True)
              (excluded F₀.character R₀) Cs Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  have high (T : Finset α) := actual_affine_high_selected_all_height_of_fibers
    (α:=T) M H hH η₀ u₀ F₀ R₀ hu₀ W hbeta μ Cs (Fintype.card α)
    hμ hμcap hCs (Fintype.card_le_of_injective (fun i : T=>i.val) Subtype.val_injective)
    (fiberReceipt T)
  choose bound hbound J hhigh using high
  have hL : 0≤3*((Fintype.card α:ℝ)+2) := by positivity
  have hb : 0≤ bΦ := by linarith
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hschedule⟩:=geometry_affine_uniform_schedule
    W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2)) bΦ (Fintype.card α) bound J
    hμ hμcap (by norm_num) hL hb (fun T k=>(hbound T k).le)
  refine ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,?_⟩
  intro T
  let P:=geometryAffineFinalHighSchedule W hWs hW μ 130 (3*((Fintype.card α:ℝ)+2))
    bΦ τ (Fintype.card α) (bound T) hμ (by norm_num) hL hb hτ (fun k=>(hbound T k).le)
  have hs:=hschedule T
  have gates : GeometryAffineHighScheduleGates W μ δ P :=
    geometry_affine_high_schedule_gates W hWs hW μ bΦ τ (Fintype.card α) (bound T)
      hμ hbΦ hτ (fun k=>(hbound T k).le)
  refine ⟨P,rfl,rfl,hs.2.1,hs.2.2.1,hs.2.2.2.1,gates,?_⟩
  exact hhigh T P hs.1 gates hs.2.2.2.2.1 hs.2.2.2.2.2.1 hs.2.2.2.2.2.2

/-- Actual source caps are fixed before the shared schedule; each literal
affine high estimate then has its constants before any moving source. -/
theorem actual_affine_high_uniform_literal_schedule_of_fibers
    (η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)(hu₀ : u₀≠0)
    (W : ℝ→ℂ)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)(hW : ContDiff ℝ ∞ W)
    (hbeta : 51/100≤ HeckeZeroSupremum.beta)
    (μ bΦ : ℝ)(hμ : 0<μ)(hμcap : μ≤1/128)(hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (μ/8) 3 1 (μ/64)) :
    let δ:=geometryAffineHighDictionaryRate μ (Fintype.card α)
    ∃τ : ℝ,0<τ ∧ τ≤μ/16 ∧ ∃g : GeometryAffineLowSchedule,
      g.μ=μ ∧ g.δ=δ ∧ g.τ=τ ∧
      ∀T : Finset α,∃P : HighSourceParameters,
        P.τ=τ ∧ P.bΦ=bΦ ∧ g.e=P.e ∧ g.κ=P.κ ∧ g.vslot=P.vslot ∧
        GeometryAffineHighScheduleGates W μ δ P ∧
        ∃Sp : Finset (ℕ×ℕ),(0,0)∈Sp ∧ ∃degree : ℕ,∃K : ℝ,0< K ∧
        ∀(Q : Ideal O)(hQM : Q≤ M)(hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)}),
          ∀ᶠZ : ℝ in atTop,2≤ Z ∧
            GeometryAffineMainHighSpec (α:=T) M H hH W hW.continuous hWs hbeta P μ δ
              (geometryAffineHighTarget μ δ) (excluded F₀.character R₀)
              Sp degree K η₀ Q hQM hQ72 Z := by
  intro δ
  obtain ⟨Cs,hCs,hcaps⟩:=eventual_actual_affine_exceptional_source_gates (α:=α) M H hH
    W hW.continuous hWs
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=actual_affine_high_uniform_schedule_of_fibers
    (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀ W hWs hW hbeta μ Cs bΦ hμ hμcap hCs hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,?_⟩
  intro T
  obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,hpaid⟩:=hhigh T
  refine ⟨P,hPτ,hPb,he,hκ,hv,gates,Sp,hSp,degree,K,hK,?_⟩
  intro Q hQM hQ72
  filter_upwards [hpaid Q hQM hQ72,hcaps,eventual_geometry_small_frequency μ hμ]
    with Z hp hc hf
  refine ⟨hp.1,?_⟩
  apply affine_main_high_spec_of_receipts (α:=T) M H hH W hW.continuous hWs hbeta
    P μ δ (geometryAffineHighTarget μ δ) (excluded F₀.character R₀) Cs Sp degree K
    η₀ Q hQM hQ72 Z hμ hμcap hf.2 _ hp.2
  unfold GeometryAffineMainLowSourceSpec
  intro θ η w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots inp
  exact geometry_affine_source_gates_actual_card inp p (Fintype.card α) Cs Z
    (hc.2 T η θ w σ freq hσ b state p t X₁ X₂ hX₁ hX₂ hw hlo₁ hlo₂ hhi₁ hhi₂ hslots)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_high_uniform_schedule_of_fibers
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_high_uniform_literal_schedule_of_fibers

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineHighUniform -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainUniform; sha256 7298f73b65687329801b51324964c73bbc87f6dd356460cab92c6858452cb8a6 -/
section
/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0. -/
                                                                     
                                                             

set_option autoImplicit false
set_option maxHeartbeats 80000
set_option maxRecDepth 2500
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter HeckeFamily CanonicalQuadraticSieve RayFourExpansion QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentOriginalCommonHarmonic CenteredMomentSecondCanonicalScalar
open CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentFiniteProfileExceptional CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondInputCapacitySource Cycle61Moment
open Cycle61Moment.LowBranch
open LocalMoment
open CenteredMomentEnergyBandMonotonicity CenteredMomentSecondEnergySplit
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentFirstAmplificationChoice
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentSecondHeightFamily
open ConcretePrimeRowBridge CompletedGauss
open Cycle61FinalNatural CenteredMomentDivisorExtraction CenteredMomentCommonRawScale
open Cycle61InitialSource CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource
open CenteredMomentEnergyState CenteredMomentEnergyBands
local notation "O" => HeckeFamily.O

variable {α : Type} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The common cutoff and the actual paid main terms are constructed from
the fixed natural source. The separate selected-fiber proof is the only
remaining high analytic premise. -/
theorem actual_affine_main_uniform_paid_of_fibers
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hbΦ : 2≤ bΦ)
    (fiberReceipt : ∀T : Finset α,
      GeometryAffineHighSelectedFiberReceipt (α:=T) η₀ u₀ F₀ R₀ (9/4) (9/4)
        (geometryLossUnit 1 εaffine/8) 3 1 (geometryLossUnit 1 εaffine/64)) :
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤ M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  let μ:=geometryLossUnit 1 εaffine
  have hμ : 0<μ:=geometry_loss_unit_pos 1 εaffine (by norm_num) hε
  have hμcap : μ≤1/128 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨τ,hτ,hτcap,g,hgμ,hgδ,hgτ,hhigh⟩:=
    actual_affine_high_uniform_literal_schedule_of_fibers (α:=α) M H hH η₀ u₀ F₀ R₀ hu₀
      W hWs hW hβlo μ bΦ hμ hμcap hbΦ fiberReceipt
  refine ⟨τ,hτ,hτcap,?_⟩
  intro Q hQM hQ hQt hQ72
  have hδ : g.δ=geometryFinalDictionaryRate g.μ 31 3 4 3 130
      (3*((Fintype.card α:ℝ)+2)) (Fintype.card α) := by
    simpa only [geometryAffineHighDictionaryRate,hgμ] using hgδ
  have hmeshμ' : mesh≤ g.μ/8 := by simpa only [hgμ] using hmeshμ
  have hmeshcap' : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (g.μ/8) := by
    simpa only [hgμ] using hmeshcap
  have hpaid:=actual_affine_main_uniform_paid_of_high (α:=α) M H hH A hc hs Sbad hbad
    W hW hWs hβlo hβhi (excluded F₀.character R₀) εaffine mesh hε hmesh hmesh0 g hgμ
    (Fintype.card α) le_rfl 130 (3*((Fintype.card α:ℝ)+2)) (by norm_num) (by positivity)
    hδ hmeshμ' hmeshcap' η₀ u₀ F₀ R₀ hu₀ η₀ Q hQM hQ hQt hQ72 (by
      intro T
      obtain ⟨P,hPτ,hPb,he,hκ,hv,gates,SH,hSH,dh,KH,hKH,hcost⟩:=hhigh T
      refine ⟨P,he.symm,hPτ.trans hgτ.symm,SH,dh,KH,hKH.le,?_⟩
      filter_upwards [hcost Q hQM hQ72] with Z hz
      simpa only [hgμ,hgδ] using hz.2)
  simpa only [hgμ] using hpaid

/-- The fixed-source main payment has no remaining analytic branch premise. -/
theorem actual_affine_main_uniform_paid
    (A : ℕ)(hc : HasCompactSupport logAnnulus)(hs : ContDiff ℝ ∞ logAnnulus)
    (Sbad : Finset (Ideal O))(hbad : fixedBadPrimes⊆Sbad)
    (W : ℝ→ℂ)(hW : ContDiff ℝ ∞ W)(hWs : Function.support W⊆Set.Icc (1:ℝ) 2)
    (hβlo : 51/100≤ HeckeZeroSupremum.beta)(hβhi : HeckeZeroSupremum.beta≤7/8)
    (η₀ : Character)(u₀ : O)(F₀ : CenteredMomentNaturalRowSource.NaturalRow η₀ u₀)
    (R₀ : Ideal O)(hu₀ : u₀≠0)
    (εaffine mesh bΦ : ℝ)(hε : 0<εaffine)
    (hmesh : mesh<(902420521/120632400000:ℝ)/2)(hmesh0 : 0≤ mesh)
    (hmeshμ : mesh≤ geometryLossUnit 1 εaffine/8)
    (hmeshcap : mesh≤ Cycle25.Energy.commonMesh 2 28 1 (geometryLossUnit 1 εaffine/8))
    (hbΦ : 2≤ bΦ)
    :
    ∃τ : ℝ,0<τ ∧ τ≤ geometryLossUnit 1 εaffine/16 ∧
    ∀(Q : Ideal O)(_hQM : Q≤ M),internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    ∀_hQ72 : internalQ Q η₀≤ Ideal.span {(72:O)},
    ∀T : Finset α,∃S : Finset (ℕ×ℕ),∃D : ℕ,∃Cm : ℝ,0≤ Cm ∧
      ∀ᶠZ : ℝ in atTop,1< Z ∧
        GeometryAffineMainPaidSpec M H hH Sbad W hW.continuous hWs
          (excluded F₀.character R₀) η₀ mesh (geometryLossUnit 1 εaffine) T S D Cm Z := by
  exact actual_affine_main_uniform_paid_of_fibers (α:=α) M H hH A hc hs Sbad hbad W hW hWs
    hβlo hβhi η₀ u₀ F₀ R₀ hu₀ εaffine mesh bΦ hε hmesh hmesh0 hmeshμ hmeshcap hbΦ
    (fun T=>geometry_affine_high_selected_fiber_receipt (α:=T) η₀ u₀ F₀ R₀ hu₀
      (geometryLossUnit 1 εaffine) (geometry_loss_unit_pos 1 εaffine (by norm_num) hε))

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_main_uniform_paid_of_fibers

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_affine_main_uniform_paid

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAffineMainUniform -/
