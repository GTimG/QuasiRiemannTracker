/- Cycle61 successor parameter adaptation by Zhongpai Gao, with AI assistance. Nominal θ=4374299/5000000, q=67/100; exact reserves and actual source consumers are changed by scoped ownership maps. Original notices/provenance remain intact. Full source replay and independent verification are pending. -/
/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B103
import Candidate.Bundles.B106
import Candidate.Bundles.B114
import Candidate.Bundles.B116
import Candidate.Bundles.B117
import Candidate.Bundles.B118
import OAI.NumberTheory.DirichletL.Energy.OriginalProfileControl
import OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPrefactorActual

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondScalarNormalization; sha256 17f30f9dc97a211a3135b2b5021ba7c93cd6fe2e012a2b3a9e369e8116027194 -/
section
                                                      
                                                         
                                                      

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentCommonProfile
open CenteredMomentSourceLiveColumn CenteredMomentFirstCanonicalFamily
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondCanonicalLedger CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonical CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O

/-- Supported frozen coefficients also give the lower child-volume bound
needed when the genuine common child's volume appears in a denominator. -/
theorem actual_common_inverse_volume {ι : Type*}[Fintype ι]
    (N : ℕ)(a : ℝ)(ha : 0< a)(s : Input ι)(hcard : Fintype.card ι≤ N)
    (hlower : a≤ s.lower)(C R : Ideal O)(B : actualAllocations s.pools C)
    (χ : Character)(t : ℝ)(hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    (volume (child s C R B χ t))⁻¹≤((min 1 a)^N)⁻¹*((C.absNorm:ℝ)/volume s) := by
  have hr := rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hv := CenteredMomentAmplificationChildInput.volume_pos s
  have ha0 : 0< min 1 a := lt_min (by norm_num) ha
  have hp : (min 1 a)^N≤(min 1 a)^(Fintype.card ι) :=
    pow_le_pow_of_le_one ha0.le (min_le_left _ _) hcard
  have hn := (actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos a s.upper ha
    (fun j x hx=>⟨hlower.trans (s.slot_support j hx).1,(s.slot_support j hx).2⟩) hne).1
  have hraw : rawReduction B.val s.P≤(C.absNorm:ℝ)/(min 1 a)^N := by
    apply (le_div_iff₀ (pow_pos ha0 N)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hp hr.le]
  rw [common_volume,inv_div]
  calc
    _≤((C.absNorm:ℝ)/(min 1 a)^N)/volume s := div_le_div_of_nonneg_right hraw hv.le
    _=_ := by ring

/-- Its fixed support constant has uniformly vanishing logarithmic cost. -/
theorem eventual_common_inverse_volume (N : ℕ)(a ε : ℝ)(ha : 0< a)(hε : 0<ε) :
    ∀ᶠZ : ℝ in atTop,1< Z ∧ ∀{ι : Type}[Fintype ι]
      (s : Input ι),Fintype.card ι≤ N → a≤ s.lower →
      ∀(C R : Ideal O)(B : actualAllocations s.pools C)(χ : Character)(t : ℝ),
      frozenCoefficient B.val C R s.ν s.W s.P≠0 →
      (volume (child s C R B χ t))⁻¹≤ Z^ε*((C.absNorm:ℝ)/volume s) := by
  filter_upwards [(tendsto_rpow_atTop hε).eventually (eventually_ge_atTop (((min 1 a)^N)⁻¹)),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro ι _ s hcard hlower C R B χ t hne
  exact (actual_common_inverse_volume N a ha s hcard hlower C R B χ t hne).trans
    (mul_le_mul_of_nonneg_right hc (div_nonneg (Nat.cast_nonneg _) (volume_pos s).le))

/-- The literal canonical scalar is exactly the common-generator norm
minus the inactive partition norm in the exponent ledger. -/
theorem actual_second_normalizer_power (C D : Ideal O)(hC : Supported C)
    (U : Finset (CommonIndex C D))(Z : ℝ)(hZ : 1< Z) :
    normalizer C D U=Z^(Real.logb Z (normValue (commonFrequencyGenerator C D))-
      Real.logb Z ((∏P∈U,P.val).absNorm:ℝ)) := by
  have hg := normValue_pos _ (commonFrequencyGenerator_ne_zero C D hC)
  have hn : (0:ℝ)<(∏P∈U,P.val).absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr (fun P _=>(commonPrime_supported_ideal C D hC P).1)))
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hg,
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn]
  exact actual_partitionNormalizer C D hC U

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_inverse_volume
#print axioms OAI.SevenEighths.Cycle61InitialMass.eventual_common_inverse_volume
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_normalizer_power

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondScalarNormalization -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondHighPayment; sha256 20d963cabcbcb44633ae2a7e7608c4633a35fdde2b50497ec32326649a970833 -/
section
                                                             
                                                                          

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ActualEisensteinCubic
open ConcretePrimeRowBridge
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstScale
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstExceptionalPrefactor
open CenteredMomentAmplifiedRetainedRadius CenteredMomentRankinRadical
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization Cycle61Moment Cycle61HighGeometry
local notation "O" => HeckeFamily.O

/-- The main radius uses the literal nominal scale, so its exponent includes
both common ideals and the inactive first projector exactly once. -/
theorem actual_main_radius_power (reflected : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (Z M A a ξ reserve : ℝ) (hZ : 1< Z) :
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l=
      Z^(2*A-c-d+R+E-M+max (d-c) 0+6*a+frequencyLoss Z 32 ξ+reserve) := by
  have hz := zero_lt_one.trans hZ
  have hc : (0:ℝ)< l.1.1.absNorm := norm_pos _ hC.1
  have hd : (0:ℝ)< l.1.2.absNorm := norm_pos _ hD.1
  have hr := active_norm_pos l.1.1 l.1.2
  have he : (0:ℝ)<(firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm := by
    exact_mod_cast firstCommonSubsetNorm_pos _ _ hC l.2.val
  have hnom : nominalLog l.1.1 l.1.2
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val})
      (Z^M) (Z^A) Z=
      2*A-Real.logb Z (l.1.1.absNorm:ℝ)-Real.logb Z (l.1.2.absNorm:ℝ)+
        Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)+
        Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)-M := by
    rw [nominalLog,nominal_equal_support _ _ _ hC.1 hD.1 heq,
      primeSubsetGenerator,span_idealGenerator]
    change Real.logb Z (((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)*
      (Ideal.span {activeConductor l.1.1 l.1.2}).absNorm*(Z^A)^2 /
      (Z^M*(l.1.1.absNorm:ℝ)*l.1.2.absNorm))=_
    simp (disch := positivity) only [Real.logb_div,Real.logb_mul,Real.logb_pow,
      Real.logb_rpow hz hZ.ne']
    ring
  dsimp only
  unfold firstMainRadius mainCommonRadius
  rw [hnom]
  congr 1
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

/-- Paying the actual main radius, second canonical normalizer, and missing
radical leaves the strict high-branch reserve. Only the explicit Fourier
and frequency slack survives. -/
theorem actual_high_scalar_payment (reflected left second : Bool) (l : FirstSourceLabel)
    (hC : Supported l.1.1) (hD : Supported l.1.2)
    (heq : primeSupport l.1.1=primeSupport l.1.2)
    (C₂ D₂ : Ideal O) (hC₂ : Supported C₂) (hD₂ : Supported D₂)
    (heq₂ : primeSupport C₂=primeSupport D₂)
    (U : Finset (CommonIndex C₂ D₂)) (Z b δ M A a ξ reserve ε : ℝ)
    (hZ : 1< Z) (hb : 3401/100000≤ b ∧ b≤1/25)
    (hδ : Cycle61.Arithmetic.q0≤δ ∧ δ≤3/4) (hM : 0≤ M)
    (hA : A≤ M*Cycle61.Arithmetic.totalA b)
    (ha : a≤ M*Cycle61.Arithmetic.amp b) :
    let ρ := LocalMoment.unmarkedDensity δ
    let c := Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ)
    let d := Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor l.1.1 l.1.2}).absNorm:ℝ)
    let E := Real.logb Z ((firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical l.1.1 l.1.2).absNorm:ℝ)
    let Lc := Real.logb Z ((Ideal.span {firstSourceNumerator left l}).absNorm:ℝ)
    let b₂ := Real.logb Z ((if second then D₂ else C₂).absNorm:ℝ)
    let ω := frequencyLoss Z 32 ξ+reserve
    let q := M-R-max (c-d) 0+Lc-6*a-ω+ε
    let m := Real.logb Z ((firstSourceMissing left l).absNorm:ℝ)
    let S := p+A-c+R+E+max (3*c-5*d-R) 0/6
    Z^(-a)*(firstMainRadius reflected (Z^M) (Z^A) Z ξ (3*a) reserve l/Z^(A-c))*
      (normalizer C₂ D₂ U/Z^b₂)*Z^(m+ρ*q+δ*(A-c-b₂)) ≤
      Z^(S-M*(781136071/45083880000000)+(1-ρ)*ω+ρ*ε) := by
  dsimp only
  rw [actual_main_radius_power reflected l hC hD heq Z M A a ξ reserve hZ,
    actual_second_normalizer_power C₂ D₂ hC₂ U Z hZ,
    actual_missing_log left l hC Z]
  have hz := zero_lt_one.trans hZ
  simp only [←Real.rpow_sub hz,←Real.rpow_add hz]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hh := actual_high_joint_excess_oriented reflected left second l hC hD
    C₂ D₂ hC₂ hD₂ heq₂ U Z b δ M A a hZ hb hδ hM hA ha
  dsimp only at hh
  have hm (c d : ℝ) : c-d+max (d-c) 0=max (c-d) 0 := by
    by_cases h : c≤ d
    · rw [max_eq_left (sub_nonneg.mpr h),max_eq_right (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)),
        max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  have hm' := hm (Real.logb Z ((if reflected then l.1.2 else l.1.1).absNorm:ℝ))
    (Real.logb Z ((if reflected then l.1.1 else l.1.2).absNorm:ℝ))
  nlinarith

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_main_radius_power

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_high_scalar_payment

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondHighPayment -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryTailChild; sha256 0d865debcff5430935ff12b4dcffd48d7c22d7c7f52f5cc2413fba7318fe69fd -/
section
                                                
                                                      
                                                     
                                                                

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentCommonAllocationSum
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceInputTailUniform
open CenteredMomentSupportedTailAggregate CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentFiniteProfileExceptional
open CenteredMomentEnergyOriginalProfileControl CenteredMomentSourceLiveColumn
open CenteredMomentCommonProfile CenteredMomentAmplificationChildSourceCaps
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O
local instance geometryTailChildDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Arbitrary second-tail saving for every first common child, with one
constant and threshold before the original source, allocation and heights. -/
theorem actual_common_child_second_tail {α : Type*}[Fintype α][DecidableEq α]
    (N : ℕ)(Cs b lo hi B ξ saving : ℝ)(hCs : 1≤ Cs)(hb : 0≤ b)
    (hlo : 0< lo)(hhi : 0≤ hi)(hB : 0≤ B)(hξ : 0<ξ) :
    ∃F : Finset (ℕ×ℕ),∃Ct : ℝ,0< Ct ∧ ∀ᶠZ : ℝ in atTop,1< Z ∧
      ∀(s : Input α),Fintype.card α≤ N → (∀i,s.M i≤ Cs) → (∀i,s.hi i≤ b) →
      ∀p : Profiles lo hi,s.W₁=p.profile 0 → s.W₂=p.profile 1 →
      ∀(C R seed : Ideal O)(alloc : actualAllocations s.pools C)(χ : Character)(t : ℝ)
        (Φ : 𝓢(ℝ,ℂ))(K Tsec : ℝ),0< K →
      volume (child s C R alloc χ t)≤ Z^B → Tsec≤ Z^B →
      (volume (child s C R alloc χ t))^2/K≤ Tsec →
      ‖secondDiscardedEnergy (child s C R alloc χ t).η (child s C R alloc χ t).t
        (original (child s C R alloc χ t) (R*C) seed).columns
        (original (child s C R alloc χ t) (R*C) seed).beta Φ K Tsec Z ξ‖ /
        volume (child s C R alloc χ t)≤
      Ct*(p.control {(0,0)})^2*F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨F,Ct,hCt,hbound⟩ := actual_subset_second_tail (α:=α) b lo hi B ξ saving hb hlo hhi hB hξ
  refine ⟨F,Ct*Cs^(2*N),mul_pos hCt (pow_pos (zero_lt_one.trans_le hCs) _),?_⟩
  filter_upwards [hbound] with Z hz
  refine ⟨hz.1,?_⟩
  intro s hn hm hs p hp₁ hp₂ C R seed alloc χ t Φ K Tsec hK hV hT hnom
  have hh := hz.2 (liveIndices alloc.val) (child s C R alloc χ t) (p.profile 0) (p.profile 1)
    hp₁ hp₂ (p.support 0) (p.support 1) (fun i=>hs i.val) (R*C) seed Φ K Tsec hK hV hT hnom
  have hc := plain_control_sq_le (child s C R alloc χ t) p ∅ N Cs hCs
    ((live_card_le alloc.val).trans hn) (fun i=>hm i.val)
  simp only [Finset.insert_empty] at hc
  have hZpos : 0< Z := zero_lt_one.trans hz.1
  apply hh.trans
  calc
    _≤ Ct*(Cs^(2*N)*(p.control {(0,0)})^2)*
        F.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
      gcongr
    _=_ := by ring

/-- A coarse polynomial bound for the literal amplified main radius. This
is used only where the discarded-frequency estimate saves arbitrary powers. -/
theorem actual_geometry_main_radius_cap {α : Type*}[Fintype α][DecidableEq α]
    (reflected : Bool)(s : Input α)(R seed : Ideal O)(M Z ξ a reserve B : ℝ)
    (hZ : 1< Z)(hK : 0< Z^M)(hB : 0≤ B)(hM : 0≤ M)
    (hA : Real.logb Z (volume s)≤ B)(ha : a≤ B)
    (hω : CenteredMomentSectorLocalization.frequencyLoss Z 32 ξ+reserve≤ B)
    (hs : Squarefree seed)(hz₁ : s.W₁ 0=0)(hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)(key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed (Z^M) Z ξ hK key)) :
    firstMainRadius reflected (Z^M) (volume s) Z ξ (3*a) reserve
      (geometryFirstLabel s R seed (Z^M) Z ξ hK key j)≤ Z^(12*B) := by
  let src := geometryFirstSource s R seed (Z^M) Z ξ hK key j.1
  let l := geometryFirstLabel s R seed (Z^M) Z ξ hK key j
  let v := geometryExponents s R seed (Z^M) Z ξ j.1.val
  let A := Real.logb Z (volume s)
  have hv (i : Fin 5) : 0≤ v i ∧ v i≤ B := by
    have hh := actual_geometry_norm_caps s R seed (Z^M) Z ξ B hs hz₁ hz₂ hsource j.1.val i
    exact ⟨Real.logb_nonneg hZ hh.1,
      (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hh.1)).mpr hh.2⟩
  have hV : volume s=Z^A := (Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (CenteredMomentAmplificationChildInput.volume_pos s)).symm
  have he : Real.logb Z (Cycle61Moment.firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=v 4 := by
    change Real.logb Z (Cycle61Moment.firstProjectorRadical l.1.1 l.1.2 l.2.val).absNorm=
      Real.logb Z (Ideal.span {ActualEisensteinCubic.primeSubsetGenerator
        (fun P : CommonIndex l.1.1 l.1.2=>P.val) l.2.val}).absNorm
    rw [Cycle61Moment.first_projector_span]
  have hR : Real.logb Z (Ideal.span {CenteredMomentCanonicalFirst.activeConductor l.1.1 l.1.2}).absNorm=v 3 := by rfl
  have hC : Real.logb Z (l.1.1.absNorm:ℝ)=v 0 := by rfl
  have hD : Real.logb Z (l.1.2.absNorm:ℝ)=v 1 := by rfl
  rw [hV,actual_main_radius_power reflected l src.hC src.hD src.sameSupport Z M A a ξ reserve hZ]
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  cases reflected <;> simp only [Bool.false_eq_true,ite_false,ite_true,hR,he,hC,hD]
  · have hmax : max (v 1-v 0) 0≤ B := max_le (by linarith [(hv 1).2,(hv 0).1]) hB
    linarith [(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2]
  · have hmax : max (v 0-v 1) 0≤ B := max_le (by linarith [(hv 0).2,(hv 1).1]) hB
    linarith [(hv 0).1,(hv 1).1,(hv 3).2,(hv 4).2]

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_child_second_tail

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_main_radius_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryTailChild -/

/- BEGIN ORIGINAL Cycle61.Moment.CanonicalFirstMask; sha256 997ccdedf565bdaab1aaff7796c9a3ba3241f6feaeb3a2c197e81f7f4ef0acd6 -/
section
                                          
                                        

set_option autoImplicit false

namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve ConcretePrimeRowBridge
open ActualEisensteinCubic CenteredMomentCanonicalFirst CenteredMomentFirstColumns
open CenteredMomentChildRows CenteredMomentNaturalRowSource CenteredMomentFirstCanonicalFamily
open CenteredMomentCommonSupport RayFourExpansion
local notation "O" => HeckeFamily.O

theorem first_signed_prime_dvd_conductor (C D : Ideal O) (hC : Supported C)
    (P : ActiveIndex C D) : firstSignedPrime C D P ∣ activeConductor C D := by
  obtain ⟨u,hu⟩ := actual_first_conductor_unit C D hC
  rw [hu]
  exact dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem (firstSignedPrime C D) (Finset.mem_univ P)) _

theorem actual_first_left_source_mask (η : Character) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff η n * coprimalityMask m n *
          leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (activeExponent C D)*ξ))
        ((u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstLeftUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_left_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstLeftCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  rw [hcoeff n hn hp, show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu 1 (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem actual_first_left_natural_parent_source_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff (excluded F₀.character R) n * coprimalityMask m n *
          leftCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (activeExponent C D)*ξ))
        (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstLeftUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_left_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstLeftCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  have hparent : χ.modulus ≤ (excluded F₀.character R).modulus := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_left
  have hpc := hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hparent)
  rw [hcoeff n hn hp, natural_parent_supported_element η u₀ n F₀ R hn hpc,
    show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem actual_first_right_source_mask (η : Character) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff η n * coprimalityMask m n *
          rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (fun P => 6-activeExponent C D P)*ξ))
        ((u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstRightUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_right_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstRightCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  rw [hcoeff n hn hp, show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu 1 (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem actual_first_right_natural_parent_source_mask (η : Character) (u₀ : O)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ : RayCharacter) :
    ∃ u : Oˣ, ∀ χ : Character,
      χ.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} →
      (∀ n : O, Supported (Ideal.span {n}) → goodLambda^2 ∣ n-1 →
        elementCoeff χ n = elementCoeff (excluded F₀.character R) n * coprimalityMask m n *
          rightCoefficient (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E)
            (activeConductor C D)
            (finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)) n *
          rayCharacter ξ n) →
      ∀ F : NaturalRow (childCharacter η (firstPhaseCharacter C D hC
          (fun P => 6-activeExponent C D P)*ξ))
        (u₀*(u:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstRightUncancelled C D),
      ∀ I : Ideal O, idealCoeff χ I =
        if IsCoprime I χ.modulus then idealCoeff F.character I else 0 := by
  obtain ⟨u,hu⟩ := actual_first_right_single_dictionary η C D hC ξ
  refine ⟨u,?_⟩
  intro χ hmod hcoeff F I
  have h72 : χ.modulus ≤ Ideal.span {(72:O)} := by
    rw [hmod]
    exact Ideal.mul_le_left.trans Ideal.mul_le_right
  apply natural_row_mask_of_primary _ χ _ F h72 _ I
  intro n hn hp hc
  have hm : χ.modulus ≤ Ideal.span {m} := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_right
  have hr : χ.modulus ≤ Ideal.span {activeConductor C D} := by
    rw [hmod]
    exact Ideal.mul_le_right.trans
      (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_left _ _))
  have hmn : IsCoprime m n := ((Ideal.isCoprime_span_singleton_iff _ _).mp
    (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hm))).symm
  have hrn : IsCoprime n (activeConductor C D) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mp
      (hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hr))
  have hholes : (∏ P ∈ firstRightCancelled C D,
      if IsCoprime n (firstSignedPrime C D P) then (1:ℂ) else 0) = 1 := by
    apply Finset.prod_eq_one
    intro P _
    exact ite_eq_left (hrn.of_isCoprime_of_dvd_right
      (first_signed_prime_dvd_conductor C D hC P))
  have hparent : χ.modulus ≤ (excluded F₀.character R).modulus := by
    rw [hmod]
    exact (Ideal.mul_le_left.trans Ideal.mul_le_left).trans Ideal.mul_le_left
  have hpc := hc.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hparent)
  rw [hcoeff n hn hp, natural_parent_supported_element η u₀ n F₀ R hn hpc,
    show coprimalityMask m n = (1:ℂ) from ite_eq_left hmn, mul_one]
  have hh := hu u₀ (primeSubsetGenerator (fun P : CommonIndex C D => P.val) E) n hn hp
  simpa only [one_mul, idealRowHom_one_supported _ hn, mul_one, hholes] using hh

theorem exists_actual_first_natural_pair_masks (η : Character) (u₀ : O) (hu₀ : u₀ ≠ 0)
    (F₀ : NaturalRow η u₀) (R : Ideal O) (m : O) (hm : m ≠ 0)
    (hmLam : goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (C D : Ideal O) (hC : Supported C) (E : Finset (CommonIndex C D))
    (ξ₁ ξ₂ : RayCharacter) :
    ∃ u₁ u₂ : Oˣ, ∃ τ₁ τ₂ : Character,
      τ₁.modulus = (excluded F₀.character R).modulus*Ideal.span {m}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          activeConductor C D} ∧
      τ₂.modulus = τ₁.modulus ∧
      ∃ h₁ : u₀*(u₁:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstLeftUncancelled C D ≠ 0,
      ∃ h₂ : u₀*(u₂:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
          firstRightUncancelled C D ≠ 0,
      (∀ I : Ideal O, idealCoeff τ₁ I = if IsCoprime I τ₁.modulus then
        idealCoeff (naturalRow (childCharacter η
          (firstPhaseCharacter C D hC (activeExponent C D)*ξ₁))
          (u₀*(u₁:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
            firstLeftUncancelled C D) h₁).character I else 0) ∧
      (∀ I : Ideal O, idealCoeff τ₂ I = if IsCoprime I τ₂.modulus then
        idealCoeff (naturalRow (childCharacter η
          (firstPhaseCharacter C D hC (fun P => 6-activeExponent C D P)*ξ₂))
          (u₀*(u₂:O)*primeSubsetGenerator (fun P : CommonIndex C D => P.val) E*
            firstRightUncancelled C D) h₂).character I else 0) := by
  obtain ⟨u₁,hleft⟩ := actual_first_left_natural_parent_source_mask η u₀ F₀ R m C D hC E ξ₁
  obtain ⟨u₂,hright⟩ := actual_first_right_natural_parent_source_mask η u₀ F₀ R m C D hC E ξ₂
  obtain ⟨τ₁,τ₂,hM₁,hM₂,hτ₁,hτ₂⟩ := exists_canonical_first_pair
    (excluded F₀.character R) m hm hmLam hm2 C D hC E ξ₁ ξ₂
  have he : primeSubsetGenerator (fun P : CommonIndex C D => P.val) E ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mp (subsetGenerator_supported C D hC E).1
  have hF₁ : firstLeftUncancelled C D ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    apply Ideal.absNorm_eq_zero_iff.not.mp
    exact (powered_numerator_norm_pos _ _ _
      (fun P _ => firstSignedPrime_supported C D hC P)).ne'
  have hF₂ : firstRightUncancelled C D ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    apply Ideal.absNorm_eq_zero_iff.not.mp
    exact (powered_numerator_norm_pos _ _ _
      (fun P _ => firstSignedPrime_supported C D hC P)).ne'
  have h₁ := mul_ne_zero (mul_ne_zero (mul_ne_zero hu₀ u₁.ne_zero) he) hF₁
  have h₂ := mul_ne_zero (mul_ne_zero (mul_ne_zero hu₀ u₂.ne_zero) he) hF₂
  refine ⟨u₁,u₂,τ₁,τ₂,hM₁,hM₂.trans hM₁.symm,h₁,h₂,?_,?_⟩
  · exact hleft τ₁ hM₁ hτ₁ _
  · exact hright τ₂ hM₂ hτ₂ _

#print axioms exists_actual_first_natural_pair_masks
#print axioms actual_first_right_source_mask
#print axioms actual_first_right_natural_parent_source_mask
#print axioms actual_first_left_natural_parent_source_mask
#print axioms actual_first_left_source_mask
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.CanonicalFirstMask -/
