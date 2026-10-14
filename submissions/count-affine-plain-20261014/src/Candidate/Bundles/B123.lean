/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B107
import Candidate.Bundles.B109
import Candidate.Bundles.B121
import Candidate.Bundles.B122
import OAI.NumberTheory.DirichletL.Energy.AllocatedProfiles

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryWidth; sha256 fc92e49fede44d0d4d827cef3bb10d871595abcb9f55386da691748881ed494f -/
section
                                                      
                                                       

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic
open CenteredMomentCanonicalFirst CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstPhysicalSource CenteredMomentCommonRadialData
open CenteredMomentCommonAllocationSum
open CenteredMomentAmplificationChildInput
open CenteredMomentSecondHeightFamily CenteredMomentSecondCanonical
open CenteredMomentSectorLocalization CenteredMomentAmplifiedRetainedRadius
open CenteredMomentSecondRadicalBudget RayFourExpansion Cycle61FinalNatural
local notation "O" => HeckeFamily.O

/-- Both geometric columns retain the exact fixed-pair modulus. -/
theorem actual_geometry_column_modulus {ι : Type*} [Fintype ι]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)
    (bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin)) :
    let src := geometryFirstSource s R seed K Z ξ hK bin j.1
    (geometryColumnCharacter reflected s R seed K Z ξ hK bin j).modulus=
      s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
        Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*
          activeConductor src.C src.D} := by
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  let F := fixedPair s.η src.C src.D src.hC src.inactive j.2.2.1 j.2.2.2⁻¹
  cases reflected
  · exact F.left_modulus
  · exact F.right_modulus

/-- Actual selected geometry gives the retained-state width in both
orientations, including the six-amplifier gain. Its only identifications
are the second datum's literal parent character and declared cutoff. -/
theorem actual_geometry_second_width {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected : Bool)(s : Input ι)(R seed : Ideal O)(K Z ξ a reserve b : ℝ)(N : ℕ)
    (hK : 0< K)(hZ : 1< Z)(hb : 0< b)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hradius : (d r.val.1).radius=frequencyRadius
      (firstMainFourierScale reflected K (volume s) Z ξ (3*a) reserve b N
        (geometryFirstLabel s R seed K Z ξ hK bin j)) Z ξ)
    (Bmask : ℝ)(χ : RayCharacter)(Q P : Ideal O)(hP : P≠0)(hPN : (P.absNorm:ℝ)≤ Z^Bmask) :
    let src := geometryFirstSource s R seed K Z ξ hK bin j.1
    let c := Real.logb Z ((if reflected then src.D else src.C).absNorm:ℝ)
    let e := Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
    let v := d r.val.1
    (retainedState Z Bmask hZ (v.τ χ) Q P hP hPN v.radius v.C v.D v.inactive).width≤
      (Real.logb Z K+Real.logb Z (s.η.modulus.absNorm:ℝ)-max (c-e) 0-6*a-
        frequencyLoss Z 32 ξ-reserve-Real.logb Z (normValue (commonFrequencyGenerator v.C v.D))+
        Real.logb Z ((∏p∈v.inactive,p.val).absNorm:ℝ))+
      (Real.logb Z fixedPresentationCost+2*(N:ℝ)*Real.logb Z b+ξ/2+
        Real.logb Z (4*(fixedFactor:ℝ))) := by
  let src := geometryFirstSource s R seed K Z ξ hK bin j.1
  have hmod := actual_geometry_column_modulus reflected s R seed K Z ξ hK bin j
  have hm : (d r.val.1).input.η.modulus=s.η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun p : CommonIndex src.C src.D=>p.val) src.inactive*
        activeConductor src.C src.D} := by rw [hparent]; exact hmod
  exact actual_second_live_main_width_oriented reflected d r s.η src.C src.D src.hC src.hD
    src.sameSupport src.inactive K (volume s) Z a (frequencyLoss Z 32 ξ) reserve ξ b N
    hK (volume_pos s) hZ hb hm Bmask χ Q P hP hPN hradius

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_column_modulus
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_second_width

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryWidth -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryNaturalState; sha256 f2034647d10cdd8145f8c4ac08e21b6e06ca7d512ef942186d9e07bf8ff2a8c0 -/
section
                                                             
                                                 

set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical
open HeckeFamily CanonicalQuadraticSieve Cycle61Moment ActualEisensteinCubic
open CenteredMomentNaturalRowSource CenteredMomentCanonicalFirst
open CenteredMomentCommonRadialData CenteredMomentSectorLocalization
open CenteredMomentChildRows CenteredMomentSecondHeightFamily RayFourExpansion
open Cycle61FinalNatural CenteredMomentEnergyState
open ConcreteTraceCRT
local notation "O" => HeckeFamily.O

/-- The natural state used by the high-density estimate is the literal
retained state of the physical row, with the appropriate signed puncture.
This connects its keep predicate, ball majorant and fixed dictionary at once. -/
theorem actual_geometry_natural_state {ι α Label : Type*}
    [Fintype ι] [Fintype α] [DecidableEq α] [Fintype Label]
    (reflected second : Bool)(η₀ : Character)(u₀ : O)(F₀ : NaturalRow η₀ u₀)(R₀ : Ideal O)
    (hu₀ : u₀≠0)(s : Input ι)(hη : s.η=excluded F₀.character R₀)
    (R seed : Ideal O)(K Z ξ : ℝ)(hK : 0< K)(hZ : 1< Z)(bin : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK bin))
    (d : Label→ SecondInputDatum α)(first : Label→ FirstSourceLabel)
    (r : secondLiveRows (fun l=>(d l).block))
    (hparent : (d r.val.1).input.η=geometryColumnCharacter reflected s R seed K Z ξ hK bin j)
    (hfirst : first r.val.1=geometryFirstLabel s R seed K Z ξ hK bin j)
    (hR : (d r.val.1).R≠0)(ψ : RayCharacter)(Bmask : ℝ)(Q : Ideal O)
    (hPN : (((d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)).absNorm:ℝ)≤ Z^Bmask)
    (m : O)(hm : m≠0)(hml : ConcretePrimeRowBridge.goodLambda∣m)(hm2 : (2:O)∣m)
    (hkeep : CenteredMomentRestrictedEnergy.nonexceptional (d r.val.1).input.η ψ Q m
      (d r.val.1).block.frequency (if second then -r.val.2.2.2.val else r.val.2.2.2.val)) :
    let unit := fun l=>(firstDictionaryUnit (!reflected) η₀ u₀ F₀ R₀ l:O)
    let hf := geometry_first_frequency_ne_zero reflected η₀ u₀ F₀ R₀ hu₀ s R seed K Z ξ hK bin j d first r hfirst
    let key₀ := secondEncodedNonzeroRow (fun l=>(d l).block) first r (!reflected) u₀ unit hf
    let key := if second then reflectedNonzeroJointLabel key₀ else key₀
    let z := if second then -r.val.2.2.2.val else r.val.2.2.2.val
    let puncture := (d r.val.1).R*(if second then (d r.val.1).D else (d r.val.1).C)
    let hP : puncture≠0 := mul_ne_zero hR (by
      split <;> first | exact (d r.val.1).hD.1 | exact (d r.val.1).hC.1)
    let st := retainedState Z Bmask hZ ((d r.val.1).τ ψ) Q puncture hP hPN
      (d r.val.1).radius (d r.val.1).C (d r.val.1).D (d r.val.1).inactive
    let holes := (d r.val.1).input.η.modulus*puncture
    st.fixedModulus=Q ∧
      st.mask=CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator puncture ∧
      holes≠0 ∧ ∃hz : st.radial.keep z,
        st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 ∧ ∀I : Ideal O,
        idealCoeff (excluded (naturalRow st.character z (st.row_ne_zero z hz)).character st.puncture) I=
        idealCoeff (excluded (naturalRow (secondFixedDictionary η₀
          (geometryDictionaryRay reflected s R seed K Z ξ hK bin j,ψ))
          (nonzeroJointSourceRow key).val (nonzeroJointSourceRow key).property).character holes) I := by
  intro unit hf key₀ key z puncture hP st holes
  have ha : st.radial.keep z ∧ st.radial.profile (‖eisEmbedding z‖^2/st.radial.scale)≠0 := by
    cases second
    · exact actual_second_live_state_admission d r Z Bmask hZ ψ Q puncture hP hPN m hm hml hm2 hkeep
    · exact actual_second_reflected_state_admission d r Z Bmask hZ ψ Q puncture hP hPN m hm hml hm2 hkeep
  have hd := actual_geometry_natural_dictionary reflected second η₀ u₀ F₀ R₀ hu₀ s hη R seed K Z ξ hK
    bin j d first r hparent hfirst hR ψ
  exact ⟨rfl,rfl,hd.1,ha.1,ha.2,hd.2⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_natural_state

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryNaturalState -/

/- BEGIN ORIGINAL Cycle61.Moment.JointShellEnergy; sha256 2a8ad2c4bcdb1193728aad9a2d391d4aa501dd74d98de343f7fb27f50c220629 -/
section
                                      
                                              

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61Moment
noncomputable section
open scoped Classical BigOperators
open Filter HeckeFamily CenteredMomentEnergyState CenteredMomentNaturalRowSource
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open Cycle61HighResidual CanonicalQuadraticSieve IdealMobiusDivisorSum LocalMoment ConcreteTraceCRT
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

lemma diagonal_retained_cost_le_pairs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Data ι) (L : Ideal O) (z : O) :
    (∑ alloc ∈ s.toSource.active L, retainedAllocationCost s L alloc z) ≤
      ∑ a ∈ s.toSource.active L, ∑ b ∈ s.toSource.active L,
        Real.sqrt (retainedAllocationCost s L a z) *
          Real.sqrt (retainedAllocationCost s L b z) := by
  apply Finset.sum_le_sum
  intro a ha
  calc
    _ = Real.sqrt (retainedAllocationCost s L a z) *
        Real.sqrt (retainedAllocationCost s L a z) :=
      (Real.mul_self_sqrt (retained_allocation_cost_nonneg s L a z)).symm
    _ ≤ _ := Finset.single_le_sum (s := s.toSource.active L)
      (f := fun b => Real.sqrt (retainedAllocationCost s L a z)*
        Real.sqrt (retainedAllocationCost s L b z))
      (fun b _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ha

/-- The buffered high support is fixed at the natural row before the residual
projector or either allocation is chosen. The actual clipping contribution
remains in the pointwise exponent through the dyad contraction. -/
theorem actual_high_retained_shell {α : Type} [Fintype α] [DecidableEq α]
    (P : HighSourceParameters) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η₀ : Character,
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
      ∀ a : ℝ, 51/100 ≤ a → a ≤ 1 → ∀ i : ℕ,
      ∀ S : Finset α, ∀ s : Data S,
      ∀ st : NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : st.fixedModulus ≤ M) (hQη : st.fixedModulus ≤ η₀.modulus)
        (z : O) (hz : st.radial.keep z),
      ∀ (w σ v : S → ℝ) (θ : S → RayQuotient.Characters M H) (ap bp : ℝ),
      ∀ Ds : Finset (Ideal O), (∀ L ∈ Ds, Squarefree L) →
      ∀ T e : ℝ, 1 ≤ T → (∀ L ∈ Ds, T ≤ (L.absNorm : ℝ)) →
      (∀ L ∈ Ds, (L.absNorm : ℝ) < 2*T) →
      (∀ L ∈ Ds, ∀ alloc ∈ s.toSource.active L, ∀ b : Bool,
        HighSourceAdmissible hH P η₀ Z a i n
          (wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
            s b L alloc w σ v θ ap bp)) →
      (∀ L ∈ Ds, ∀ alloc ∈ s.toSource.active L, ∀ b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
          s b L alloc w σ v θ ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
          Cycle61.Physical.sourcePostClip s.toSource b Z L alloc ≤ e) →
      (∑ L ∈ Ds, ∑ alloc ∈ s.toSource.active L,
        retainedAllocationCost s L alloc z) ≤
      C*(wholeControl s)^2*(2*T)^(2*ε)*
        Z^(e+s.toSource.allowance Z+
          Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂]) := by
  obtain ⟨n,Cp,Cs,hCp,hCs,hactual⟩ := actual_high_source_datum M H hH P
  obtain ⟨Csh,hCsh,hshell⟩ := uniform_retained_pair_shell (ι := α) ε hε
  let K := Cp^2*(max 1 Cs)^(Fintype.card α)
  have hK : 0 < K := mul_pos (sq_pos_of_pos hCp)
    (pow_pos (zero_lt_one.trans_le (le_max_left _ _)) _)
  refine ⟨n,4*K*Csh,by positivity,?_⟩
  intro η₀
  filter_upwards [hactual η₀] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro a ha ha' i S s st hQM hQη z hz w σ v θ ap bp Ds hDs T e hT hlo hhi hvalid hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hpoint (L : Ideal O) (hL : L ∈ Ds)
      (alloc : Allocation L (Finset.univ : Finset (S ⊕ Fin 2)))
      (halloc : alloc ∈ s.toSource.active L) (b : Bool) :
      (normalizedPositiveNorm s.toSource b Z L alloc z)^2 ≤ K*Z^e := by
    let D := wholeHighDatum M H hH P η₀ Z st hQM hQη z hz
      s b L alloc w σ v θ ap bp
    have hcard : D.liveCard P ≤ Fintype.card α := by
      change (liveIndices L alloc).card ≤ Fintype.card α
      exact (Finset.card_le_univ _).trans (by simpa using Finset.card_le_univ S)
    have hc := high_source_datum_cap M H P hZ.1.le hCs.le (by linarith : 1/2 ≤ a)
      (hZ.2 a ha ha' i D (hvalid L hL alloc halloc b)) le_rfl hcard
    have hn := normalizedPositiveNorm_sq_bound s.toSource b Z hZp L alloc z K
      ((2*a-1)*D.total P+2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α))
      (by convert hc using 1; rfl)
    exact hn.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le (hexp L hL alloc halloc b)) hK.le)
  have hpairs (L : Ideal O) (hL : L ∈ Ds)
      (x : Allocation L (Finset.univ : Finset (S ⊕ Fin 2))) (hx : x ∈ s.toSource.active L)
      (y : Allocation L (Finset.univ : Finset (S ⊕ Fin 2))) (hy : y ∈ s.toSource.active L)
      (b c : Bool) :
      normalizedPositiveNorm s.toSource b Z L x z *
        normalizedPositiveNorm s.toSource c Z L y z ≤ K*Z^e := by
    have hhx := hpoint L hL x hx b
    have hhy := hpoint L hL y hy c
    nlinarith [sq_nonneg (normalizedPositiveNorm s.toSource b Z L x z-
      normalizedPositiveNorm s.toSource c Z L y z)]
  have hbound := hshell S S s s Ds hDs (fun _ _ _=>z) (fun _ _ _=>z) T Z
    hT hZ.1 hlo hhi (fun _ _=>K*Z^e) (fun _ _=>by positivity) hpairs
  calc
    _ ≤ ∑ L ∈ Ds, ∑ x ∈ s.toSource.active L, ∑ y ∈ s.toSource.active L,
        Real.sqrt (retainedAllocationCost s L x z)*
          Real.sqrt (retainedAllocationCost s L y z) :=
      Finset.sum_le_sum (fun L _=>diagonal_retained_cost_le_pairs s L z)
    _ ≤ _ := hbound.trans_eq (by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_bool, Nat.cast_ofNat,
        nsmul_eq_mul]
      rw [show e+s.toSource.allowance Z+Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂] =
        e+(s.toSource.allowance Z+s.toSource.allowance Z+
          Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂]+
          Cycle61.Physical.plainClipAllowance Z ![s.b₁,s.b₂])/2 by ring,
        Real.rpow_add hZp]
      ring)


/-- Residual allocations are contracted at each fixed encoded row; only
then is the joint physical pool counted by the fixed natural dictionary. -/
theorem actual_high_joint_shell_energy {α Base : Type} [Fintype α] [DecidableEq α]
    [Fintype Base] (base : Base → Character) (η₀ : Character)
    (B Q loss ε : ℝ) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hloss : 0 < loss) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ P : HighSourceParameters, ∃ n : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 2 ≤ Z ∧
      ∀ (left : Bool) (u₀ : O) (unit : FirstSourceLabel → O)
        (q m a e allowance Kcontrol T ap bp : ℝ) (i : ℕ),
      q ≤ Q → 33/40 ≤ a → a ≤ 7/8 → 0 ≤ Kcontrol → 1 ≤ T →
      ∀ labels : Finset (NonzeroJointSourceLabel left u₀ unit),
      ∀ st : NonzeroJointSourceLabel left u₀ unit → NaturalState Z P.Bmask P.bΦ,
      ∀ (hQM : ∀ l, (st l).fixedModulus ≤ M) (hQη : ∀ l, (st l).fixedModulus ≤ η₀.modulus)
        (z : NonzeroJointSourceLabel left u₀ unit → O) (hz : ∀ l, (st l).radial.keep (z l))
        (index : NonzeroJointSourceLabel left u₀ unit → Base)
        (holes : NonzeroJointSourceLabel left u₀ unit → Ideal O),
      (∀ l ∈ labels, holes l ≠ 0) →
      (∀ l ∈ labels, ∀ I : Ideal O,
        idealCoeff (excluded (naturalRow (st l).character (z l)
          ((st l).row_ne_zero (z l) (hz l))).character (st l).puncture) I =
        idealCoeff (excluded (naturalRow (base (index l)) (nonzeroJointSourceRow l).val
          (nonzeroJointSourceRow l).property).character (holes l)) I) →
      (∀ l ∈ labels, rawFrequencyNorm (nonzeroJointSourceRow l) ≤ Z^q ∧
        a ≤ HeckeDetectorZeros.zeroMaximum
          (wholeSourceFamily M H hH η₀ (excluded
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))).character
              (st l).puncture))
          (whole_source_family_nonprincipal M H hH (st l) η₀ (hQM l) (hQη l) (z l) (hz l)
            (naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l))))
          (3*(i+1 : ℕ)*Z^P.τ)) →
      (∀ l ∈ labels, Supported l.val.1.1.1 ∧ l.val.1.1.2 ≠ 0 ∧
        Supported l.val.2.1.1 ∧ l.val.2.1.2 ≠ 0) →
      (∀ l ∈ labels, primeSupport l.val.1.1.1 = primeSupport l.val.1.1.2 ∧
        primeSupport l.val.2.1.1 = primeSupport l.val.2.1.2) →
      (∀ l ∈ labels, ((Ideal.span {jointSourceRow left u₀ unit l.val}*
        firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, (l.val.1.1.1.absNorm : ℝ) ≤ Z^B ∧
        (l.val.1.1.2.absNorm : ℝ) ≤ Z^B ∧
        (l.val.2.1.1.absNorm : ℝ) ≤ Z^B ∧ (l.val.2.1.2.absNorm : ℝ) ≤ Z^B) →
      (∀ l ∈ labels, ((firstSourceMissing left l.val.1).absNorm : ℝ) ≤ Z^m) →
      ∀ (S : NonzeroJointSourceLabel left u₀ unit → Finset α)
        (s : ∀ l, Data (S l)) (w σ v : ∀ l, S l → ℝ)
        (θ : ∀ l, S l → RayQuotient.Characters M H)
        (Ds : NonzeroJointSourceLabel left u₀ unit → Finset (Ideal O)),
      (∀ l ∈ labels, ∀ L ∈ Ds l, Squarefree L) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, T ≤ (L.absNorm : ℝ) ∧ (L.absNorm : ℝ) < 2*T) →
      (∀ l ∈ labels, (wholeControl (s l))^2 ≤ Kcontrol) →
      (∀ l ∈ labels, (s l).toSource.allowance Z+
        Cycle61.Physical.plainClipAllowance Z ![(s l).b₁,(s l).b₂] ≤ allowance) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        HighSourceAdmissible hH P η₀ Z a i n
          (wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
            (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp)) →
      (∀ l ∈ labels, ∀ L ∈ Ds l, ∀ alloc ∈ (s l).toSource.active L, ∀ b : Bool,
        (2*a-1)*(wholeHighDatum M H hH P η₀ Z (st l) (hQM l) (hQη l) (z l) (hz l)
          (s l) b L alloc (w l) (σ l) (v l) (θ l) ap bp).total P+
          2*P.εplain*P.d+2*P.εslot*P.d*(Fintype.card α)-
          Cycle61.Physical.sourcePostClip (s l).toSource b Z L alloc ≤ e) →
      (∑ l ∈ labels, ∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤
      C*Kcontrol*(1+3*(i+1 : ℕ)*Z^P.τ)^J*(2*T)^(2*ε)*
        Z^(m+q*unmarkedDensity (2*a-1)+loss+e+allowance) := by
  obtain ⟨J,Ccount,hCcount,hcount⟩ := actual_whole_joint_high_row_count M H hH
    base η₀ B Q loss hB hQ hQB hloss
  refine ⟨J,?_⟩
  intro P
  obtain ⟨n,Cshell,hCshell,hactual⟩ := actual_high_retained_shell (α := α) M H hH P ε hε
  refine ⟨n,Ccount*Cshell,mul_pos hCcount hCshell,?_⟩
  filter_upwards [hactual η₀,eventually_ge_atTop (2 : ℝ)] with Z hZ hZ₂
  refine ⟨hZ₂,?_⟩
  intro left u₀ unit q m a e allowance Kcontrol T ap bp i hq ha ha' hK hT
    labels st hQM hQη z hz index holes hholes hmask hzero hsupported heq hsupport hnorm
    hmissing S s w σ v θ Ds hDs hdyad hcontrol hallowance hvalid hexp
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hTshared : 0 ≤ 3*(i+1 : ℕ)*Z^P.τ := by positivity
  have hcard := hcount left u₀ unit Z hZ₂ q m a (3*(i+1 : ℕ)*Z^P.τ)
    P.Bmask P.bΦ hq ha ha' hTshared labels st hQM hQη z hz
    (fun l => naturalRow (st l).character (z l) ((st l).row_ne_zero (z l) (hz l)))
    index holes hholes hmask hzero hsupported heq hsupport hnorm hmissing
  let W := Cshell*Kcontrol*(2*T)^(2*ε)*Z^(e+allowance)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hpoint (l : NonzeroJointSourceLabel left u₀ unit) (hl : l ∈ labels) :
      (∑ L ∈ Ds l, ∑ alloc ∈ (s l).toSource.active L,
        retainedAllocationCost (s l) L alloc (z l)) ≤ W := by
    have hr := hZ.2 a (by linarith : 51/100 ≤ a) (by linarith : a ≤ 1) i (S l) (s l)
      (st l) (hQM l) (hQη l) (z l) (hz l) (w l) (σ l) (v l) (θ l) ap bp
      (Ds l) (hDs l hl) T e hT (fun L hL => (hdyad l hl L hL).1)
      (fun L hL => (hdyad l hl L hL).2) (hvalid l hl) (hexp l hl)
    apply hr.trans
    dsimp [W]
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcontrol l hl) hCshell.le)
        (Real.rpow_nonneg (by positivity) _)
    · exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith [hallowance l hl])
    · positivity
    · positivity
  calc
    _ ≤ ∑ _l ∈ labels, W := Finset.sum_le_sum hpoint
    _ = (labels.card : ℝ)*W := by simp [nsmul_eq_mul]
    _ ≤ (Ccount*(1+3*(i+1 : ℕ)*Z^P.τ)^J*
        Z^(m+q*unmarkedDensity (2*a-1)+loss))*W :=
      mul_le_mul_of_nonneg_right hcard hW
    _ = _ := by
      dsimp [W]
      rw [show m+q*unmarkedDensity (2*a-1)+loss+e+allowance =
        (m+q*unmarkedDensity (2*a-1)+loss)+(e+allowance) by ring,
        Real.rpow_add hZp (m+q*unmarkedDensity (2*a-1)+loss) (e+allowance)]
      ring

#print axioms actual_high_joint_shell_energy

#print axioms actual_high_retained_shell
#print axioms diagonal_retained_cost_le_pairs
end
end OAI.SevenEighths.Cycle61Moment

end
/- END ORIGINAL Cycle61.Moment.JointShellEnergy -/

/- BEGIN ORIGINAL Cycle61.Physical.FinalProfiles; sha256 81f958f7633f7a7b014011b9b22376f41e5f38718af714a0fdacb720122b8719 -/
section
                                                           

set_option autoImplicit false
namespace OAI.SevenEighths.Cycle61FinalProfiles
noncomputable section
open scoped Classical SchwartzMap
open CenteredMomentFiniteProfileExceptional CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile

/-- On a surviving rectangle, the retained pair is exactly the two clipped
plain profiles used by the literal positive-row energy. -/
theorem actual_clipped_pair (a b : ℝ) (ha : 0< a) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀i,0< U i) (hret : ∀i,1≤ U i*b) (i : Fin 2) :
    ((retainedPair a b ha p U hU 0).profile i : ℝ→ℂ) =
      dilated (p.profile i) (clipDilation (U i)) := by
  funext x
  change (sourcePlain a b ha (p.profile i) (p.support i)).profile (U i) (hU i) 0 x = _
  rw [Plain.profile_retained _ _ _ _ (hret i)]
  simpa only [sourcePlain,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul,dilated] using
    retainedProfile_apply (p.profile i) a b ha (p.support i) ((p.profile i).smooth ⊤)
      (U i) (hU i) (hret i) 0 x

/-- The finite seminorm controls are chosen before both moving clipping
scales. At zero extra height the old uniform bound has no height loss. -/
theorem clipped_pair_control (a b : ℝ) (ha : 0< a) (S : Finset (ℕ×ℕ)) :
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
      ∀p:Profiles a b,∀U:Fin 2→ℝ,∀hU:∀i,0< U i,
      (retainedPair a b ha p U hU 0).control S≤ C*p.control T := by
  obtain ⟨n,T,C,hC,hbound⟩ := retained_pair_control a b ha S
  refine ⟨T,C,hC,?_⟩
  intro p U hU
  simpa using hbound p U hU 0

end
end OAI.SevenEighths.Cycle61FinalProfiles
#print axioms OAI.SevenEighths.Cycle61FinalProfiles.actual_clipped_pair
#print axioms OAI.SevenEighths.Cycle61FinalProfiles.clipped_pair_control

end
/- END ORIGINAL Cycle61.Physical.FinalProfiles -/
