/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B080
import Candidate.Bundles.B083
import OAI.NumberTheory.DirichletL.Energy.FirstAnnularAdmission
import OAI.NumberTheory.DirichletL.Moments.ActiveDivisorShell
import OAI.NumberTheory.DirichletL.Moments.DivisorRetained
import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.JointAmplification; sha256 be0fef82b55e52f05ed069fa375f28a01239aa61e2b4289a0785c888f515110a -/
section
                                                 

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge ConcreteTraceCRT
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstSourceReduction CenteredMomentFirstReferenceSource
open CenteredMomentFirstAnnularInput CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplificationErrorEnergy CenteredMomentAmplificationGlobal
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationRadicalChoice
open CenteredMomentPrimeElements CenteredMomentPrimePool CenteredMomentGaussEnergy
open CenteredMomentFirstScale CenteredMomentSourceRow CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSecondHeightFamily
open CenteredMomentFirstPhysicalSource CenteredMomentFirstCommonSourceBudget
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstRetainedNorm CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentFirstDiscardedEnergy CenteredMomentSourceLiveColumn
open CenteredMomentFirstAllocationGaussEnergy CenteredMomentSectorLocalization
open CenteredMomentAmplifiedRetainedRadius CenteredMomentAmplificationActiveFactor
open CenteredMomentChildRows RayFourExpansion CenteredMomentCommonProfile
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance jointAmplificationDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- The amplification threshold precedes every surviving subset of the
original slot set. Heterogeneous live allocations retain one joint sum. -/
theorem actual_subset_matched_source_amplification
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec ξ reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b)
    (hgap : eta< sigma/6) (hC : 1≤ Csec) (hξ : 0≤ξ) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀{Label : Type*} [Fintype Label],
    ∀slots : Label→ Finset ι, ∀s : (j : Label)→ Input (slots j), ∀g : Label→ FirstBranchGeometry, ∀weight : Label→ℝ,
      (∀j,0≤ weight j) → (∀j,g j |>.Eligible Z BR Bs Mmax Csec ξ) →
      (∀j,∀i,Function.support ((s j).W i)⊆Set.Iic b) →
    ∀z : (j : Label)→ slots j→ℝ, (∀j i,z j i≤ eta) → (∀j i,(s j).P i=Z^(z j i)) →
    ∃τ : Label→ elementPool P→ Fin 3→ RayCharacter→ Character,
      (∀j p i χ,(τ j p i χ).modulus.absNorm≤
        radicalBound (childCharacter (s j).η χ) fixedBadMask p.val
          (errorMovingExponent (errorIndex i))) ∧
      (∑j,weight j*normalizedGaussSource (s j) (g j).R (g j).seed
        CenteredMomentFirstAnnularMajorant.profile (g j).H0) ≤
      (56/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*(∑j,weight j*actualMainSource (s j) (g j) Z sigma Csec ξ reserve)+
          ∑j,weight j*actualErrorSources (s j) (g j) Z sigma Csec ξ reserve P (τ j)) := by
  have hall := Filter.eventually_all.mpr (fun T : Finset ι=>
    eventually_input_amplification (ι:=T) rayM H hH Sbad hbad
      sigma loss BR Bs Mmax b eta Csec ξ reserve hsigma hloss hM hb hgap hC hξ hreserve)
  filter_upwards [hall] with Z hz
  obtain ⟨hZ,hP,hcard,_⟩ := hz ∅
  refine ⟨hZ,hP,hcard,?_⟩
  intro Label _ slots s g weight hw hg hsupp z hzslot hlen
  choose τ hN henergy using (fun j => (hz (slots j)).2.2.2 (s j).η)
  refine ⟨τ,hN,?_⟩
  have hbranch (j : Label) := henergy j (s j) rfl (hsupp j) (z j) (hzslot j) (hlen j)
    (g j).R (g j).seed (hg j).1 (hg j).2.1 (hg j).2.2.1 (hg j).2.2.2.1
    (g j).d (g j).cLog (g j).I (g j).J (g j).E (hg j).2.2.2.2.1
    (g j).K (g j).X (g j).Tsec (hg j).2.2.2.2.2.1 (hg j).2.2.2.2.2.2.1
    (hg j).2.2.2.2.2.2.2.1 (g j).H0 (hg j).2.2.2.2.2.2.2.2.1
    (hg j).2.2.2.2.2.2.2.2.2.1 (hg j).2.2.2.2.2.2.2.2.2.2
  have hh := Finset.sum_le_sum (s:=Finset.univ)
    (fun j _ => mul_le_mul_of_nonneg_left (hbranch j) (hw j))
  apply hh.trans_eq
  change (∑j,weight j*((56/_)*(_*actualMainSource (s j) (g j) Z sigma Csec ξ reserve+
    actualErrorSources (s j) (g j) Z sigma Csec ξ reserve _ (τ j))))=_
  simp_rw [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring


/-- Amplify the actual common-allocation children in one finite sum. The
slot exponents and support are inherited from the original source, while
both source characters and Mellin heights may vary with the first label. -/
theorem actual_common_children_amplification
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤ H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec ξ reserve : ℝ)
    (hsigma : 0< sigma) (hloss : 0< loss) (hM : 0≤ Mmax) (hb : 0≤ b)
    (hgap : eta< sigma/6) (hC : 1≤ Csec) (hξ : 0≤ξ) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1< Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀{Label : Type*} [Fintype Label], ∀s : Input ι, ∀R : Ideal O,
    ∀C : Label→ Ideal O, ∀g : Label→ FirstBranchGeometry, ∀χ : Label→ Character,
    ∀t : Label→ℝ, ∀weight : (j : Label)→ actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤ weight j B) → (∀j,(g j).R=R*C j) →
      (∀j,(g j).Eligible Z BR Bs Mmax Csec ξ) →
      (∀i,Function.support (s.W i)⊆Set.Iic b) →
    ∀z : ι→ℝ, (∀i,z i≤ eta) → (∀i,s.P i=Z^(z i)) →
    ∃τ : (j : Label)→ actualAllocations s.pools (C j)→ elementPool P→ Fin 3→ RayCharacter→ Character,
      (∀j B p i ψ,(τ j B p i ψ).modulus.absNorm≤
        radicalBound (childCharacter (χ j) ψ) fixedBadMask p.val
          (errorMovingExponent (errorIndex i))) ∧
      (∑j,∑B,weight j B*childNormalizedGaussSource s (C j) R (g j).seed B (χ j) (t j)
        CenteredMomentFirstAnnularMajorant.profile (g j).H0) ≤
      (56/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          (∑j,∑B,weight j B*actualMainSource (child s (C j) R B (χ j) (t j))
            (g j) Z sigma Csec ξ reserve)+
          ∑j,∑B,weight j B*actualErrorSources (child s (C j) R B (χ j) (t j))
            (g j) Z sigma Csec ξ reserve P (τ j B)) := by
  filter_upwards [actual_subset_matched_source_amplification (ι:=ι)
    rayM H hH Sbad hbad sigma loss BR Bs Mmax b eta Csec ξ reserve
    hsigma hloss hM hb hgap hC hξ hreserve] with Z hz
  refine ⟨hz.1,hz.2.1,hz.2.2.1,?_⟩
  intro Label _ s R C g χ t weight hw hR hg hsupp z hzslot hlen
  let Index := (j : Label) × actualAllocations s.pools (C j)
  let slots (q : Index) := liveIndices q.2.val
  let inp (q : Index) : Input (slots q) := child s (C q.1) R q.2 (χ q.1) (t q.1)
  obtain ⟨τ,hτ,he⟩ := hz.2.2.2 slots inp (fun q=>g q.1) (fun q=>weight q.1 q.2)
    (fun q=>hw q.1 q.2) (fun q=>hg q.1) (fun _ i=>hsupp i.val)
    (fun _ i=>z i.val) (fun _ i=>hzslot i.val) (fun _ i=>hlen i.val)
  refine ⟨fun j B=>τ ⟨j,B⟩,fun j B p i ψ=>hτ ⟨j,B⟩ p i ψ,?_⟩
  simpa only [Index,inp,Fintype.sum_sigma,hR,childNormalizedGaussSource] using he

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_subset_matched_source_amplification

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_common_children_amplification

end
/- END ORIGINAL Cycle61.Physical.InitialMass.JointAmplification -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.GeometryAdmission; sha256 8d81ccb1da2665d5b83566274068f123240099fba62191677fada3dac2fa509e -/
section
                                                   
                                                      
                                                               
                                                            

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentFirstPhysicalSource
open CenteredMomentFirstCanonicalFamily CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstReferenceSource CenteredMomentFirstScale CenteredMomentCommonSupport
open CenteredMomentSourceRow CenteredMomentWholeDivisorShell CenteredMomentSourceMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentSectorLocalization
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentFirstNonexceptionalWeightSum
open CenteredMomentFirstSectors CenteredMomentCanonicalFirst
local notation "O" => HeckeFamily.O

/-- A first residual projector divides an actual column. This uses a bound
on the actual finite pool, not an assertion that every padded column has
nonzero coefficient. -/
theorem first_divisor_norm (s : FirstBlockSource) (Y : ℝ)
    (hpool : ∀I∈s.pool,(I.absNorm:ℝ)≤ Y) (L : s.divisors) :
    L.val≠0 ∧ (L.val.absNorm:ℝ)≤ Y := by
  apply divisorPool_nonzero_norm Finset.univ
    (fun i : s.RightIndex=>Ideal.span {element s.C s.D s.hD.1 s.pool i})
    (fun i _=>by rw [element_span];exact (column_supported _ _ _ _ i).1) Y _ L.val L.property
  intro i _
  rw [element_span]
  have hmem := (mem_residualPool s.D s.hD.1 (supportedColumns s.pool) i.val).mp
    (Finset.mem_filter.mp i.property).1
  have hd : s.D*i.val≠0 := (Finset.mem_filter.mp hmem).2.1
  exact (CenteredMomentFirstSourceConductorCaps.divisor_norm_le i.val (s.D*i.val) hd
    (dvd_mul_left _ _)).trans (hpool _ (Finset.mem_filter.mp hmem).1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryAdmissionDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _


omit [DecidableEq ι] in
/-- A coarse finite-pool bound is sufficient for amplifier admission. It
includes padded zero-coefficient columns and costs no source-mass factor. -/
theorem actual_finite_pool_cap (s : Input ι) (N : ℕ) (Z U : ℝ)
    (hN : Fintype.card ι≤ N) (hZ : 1≤ Z) (hU : 0≤ U)
    (hpool : ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Z^U) :
    ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤ Z^(((N:ℝ)+2)*U) := by
  intro I hI
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hI
  have he : ((CenteredMomentAddedZeroUniform.finiteTupleProduct v).absNorm:ℝ)=
      ∏j,((v j).absNorm:ℝ) := by
    simp only [CenteredMomentAddedZeroUniform.finiteTupleProduct,map_prod,Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∏_j : ι⊕Fin 2,Z^U :=
      Finset.prod_le_prod₀ (fun _ _=>Nat.cast_nonneg _)
        (fun j _=>hpool j (v j) ((Fintype.mem_piFinset.mp hv) j))
    _ = Z^(((Fintype.card ι:ℝ)+2)*U) := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
      rw [←Real.rpow_mul_natCast (zero_le_one.trans hZ)]
      congr 1
      push_cast
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul_of_nonneg_right (show (Fintype.card ι:ℝ)+2≤(N:ℝ)+2 by
        exact_mod_cast Nat.add_le_add_right hN 2) hU)

omit [DecidableEq ι] in
/-- The standard completed plain pools obey their advertised cutoff even
when they include values at which the smooth profile vanishes. -/
theorem actual_completed_pool_cap (s : Input ι) (Y : ℝ)
    (hslot : ∀i I,I∈s.slots i→(I.absNorm:ℝ)≤ Y)
    (hp₁ : s.plain₁=CenteredMomentSourceRectangle.plainSupportPool s.b₁ s.X₁ s.Y₁)
    (hp₂ : s.plain₂=CenteredMomentSourceRectangle.plainSupportPool s.b₂ s.X₂ s.Y₂)
    (hx₁ : s.b₁*s.X₁≤ Y) (hy₁ : s.b₁*s.Y₁≤ Y)
    (hx₂ : s.b₂*s.X₂≤ Y) (hy₂ : s.b₂*s.Y₂≤ Y) :
    ∀j I,I∈s.pools j→(I.absNorm:ℝ)≤ Y := by
  intro j I hi
  cases j with
  | inl i => exact hslot i I hi
  | inr i =>
    fin_cases i
    · change I∈s.plain₁ at hi
      rw [hp₁] at hi
      rcases Finset.mem_union.mp hi with hx|hy
      · exact ((mem_idealBall _ _).mp hx).2.trans hx₁
      · exact ((mem_idealBall _ _).mp hy).2.trans hy₁
    · change I∈s.plain₂ at hi
      rw [hp₂] at hi
      rcases Finset.mem_union.mp hi with hx|hy
      · exact ((mem_idealBall _ _).mp hx).2.trans hx₂
      · exact ((mem_idealBall _ _).mp hy).2.trans hy₂

def geometryBranch (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ : ℝ) (hK : 0< K) (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) : FirstBranchGeometry :=
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  { R := R*geometryColumnIdeal reflected s R seed K Z ξ hK key j
    seed := j.2.1.val
    I := src.C
    J := src.D
    E := Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive}
    d := Real.logb Z ((if reflected then src.C else src.D).absNorm:ℝ)
    cLog := Real.logb Z ((geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)
    K := K
    X := volume s.toData
    Tsec := firstNominalScale src.C src.D
      (Ideal.span {primeSubsetGenerator (fun P : CommonIndex src.C src.D=>P.val) src.inactive})
      K (volume s.toData)
    H0 := src.H0 }

omit [DecidableEq ι] in
/-- Actual live first columns satisfy amplification's geometric gates.
Both reflected and unreflected columns retain the original annular scale. -/
theorem actual_geometry_admission (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ A D ξcap B BR Bs : ℝ) (hK : 0< K) (hZ : 32≤ Z)
    (hξ : ξ≤ξcap) (hV : volume s.toData≤ Z^A) (hKi : K⁻¹≤ Z^D)
    (hR : R≠0) (hRn : (R.absNorm:ℝ)≤ Z^BR)
    (hs : Squarefree seed) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsource : sourceRadius s≤ Z^B)
    (hpool : ∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤ Z^Bs)
    (key : ℤ×(Fin 5→ℤ))
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key)) :
    (geometryBranch reflected s R seed K Z ξ hK key j).Eligible
      Z (BR+B) Bs (amplifierCap A D ξcap) 1 ξ := by
  let src := geometryFirstSource s R seed K Z ξ hK key j.1
  have hC : Supported (geometryColumnIdeal reflected s R seed K Z ξ hK key j) := by
    cases reflected
    · exact src.hC
    · exact src.hD
  have hn : ((geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)≤ Z^B := by
    cases reflected
    · exact (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 0).2
    · exact (actual_geometry_norm_caps s R seed K Z ξ B hs hz₁ hz₂ hsource j.1.val 1).2
  have hL := first_divisor_norm src (Z^Bs) hpool j.2.1
  have he := (subsetGenerator_supported src.C src.D src.hC src.inactive).1
  have hh := source_amplifier_packet A D ξcap Z hZ s R seed K ξ hK hξ hV hKi
    j.1.val.1 j.1.val.2.1.val j.1.val.2.2
  rw [source_nominal_span] at hh
  refine ⟨mul_ne_zero hR hC.1,hL.1,?_,hL.2,he,hK,
    volume_pos s.toData,(by simp [geometryBranch]),src.H0_pos,hh.2.2.1,hh.2.2.2.1⟩
  change ((R*geometryColumnIdeal reflected s R seed K Z ξ hK key j).absNorm:ℝ)≤ Z^(BR+B)
  rw [map_mul,Nat.cast_mul,Real.rpow_add (by linarith : 0< Z)]
  exact mul_le_mul hRn hn (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.first_divisor_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_geometry_admission

#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_finite_pool_cap
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_completed_pool_cap

end
/- END ORIGINAL Cycle61.Physical.InitialMass.GeometryAdmission -/

/- BEGIN ORIGINAL Cycle61.Physical.ClippedProjector; sha256 8716adfa30af180e90e6e5646c15ada193b308c9b05aeb517824814323a77bbf -/
section
                                                          

namespace Cycle61.Physical

noncomputable section
open scoped BigOperators Classical
open OAI OAI.SevenEighths
open CenteredMomentDivisorAllocation CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorExtraction
local notation "O" => ActualEisensteinCubic.O

def negativeTotal (x : Fin 2 → ℝ) : ℝ := ∑ i, max 0 (-x i)

def clippedReduction (r : ℝ) (x a : Fin 2 → ℝ) : ℝ :=
  r - (negativeTotal (fun i => x i-a i)-negativeTotal x)

theorem negative_clip_gain (x a : ℝ) (ha : 0 ≤ a) :
    0 ≤ max 0 (-(x-a))-max 0 (-x) ∧
      max 0 (-(x-a))-max 0 (-x) ≤ a := by
  have hmono : max 0 (-x) ≤ max 0 (-(x-a)) := max_le_max (le_refl _) (by linarith)
  have hupper : max 0 (-(x-a)) ≤ a+max 0 (-x) := by
    apply max_le
    · linarith [le_max_left (0:ℝ) (-x)]
    · linarith [le_max_right (0:ℝ) (-x)]
  constructor <;> linarith

theorem clippedReduction_nonneg (r : ℝ) (x a : Fin 2 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hr : ∑ i, a i ≤ r) :
    0 ≤ clippedReduction r x a := by
  have hs : negativeTotal (fun i => x i-a i)-negativeTotal x ≤ ∑ i, a i := by
    rw [negativeTotal, negativeTotal, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ => (negative_clip_gain (x i) (a i) (ha i)).2)
  unfold clippedReduction
  linarith

theorem clippedReduction_le_raw (r : ℝ) (x a : Fin 2 → ℝ)
    (ha : ∀ i, 0 ≤ a i) : clippedReduction r x a ≤ r := by
  have hs : 0 ≤ negativeTotal (fun i => x i-a i)-negativeTotal x := by
    rw [negativeTotal, negativeTotal, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg (fun i _ => (negative_clip_gain (x i) (a i) (ha i)).1)
  unfold clippedReduction
  linarith

/-- The clipped exponent is attached to each positive rectangle separately. -/
theorem extraction_scalar_identity (r e : ℝ) (x a : Fin 2 → ℝ) :
    (-clippedReduction r x a+e+negativeTotal x)/2 =
      (-r+e+negativeTotal (fun i => x i-a i))/2 := by
  unfold clippedReduction
  ring

theorem extraction_scalar_rpow (Z r e : ℝ) (hZ : 0 < Z) (x a : Fin 2 → ℝ) :
    Z^(-r/2)*Z^((e+negativeTotal (fun i => x i-a i))/2) =
      Z^((-clippedReduction r x a+e+negativeTotal x)/2) := by
  rw [← Real.rpow_add hZ, extraction_scalar_identity]
  congr 1
  ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualPlainReduction (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (j : Fin 2) : ℝ :=
  Real.logb Z (Ideal.absNorm (selectedPlain D a j) : ℝ)

theorem actual_plain_reduction_nonneg (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (j : Fin 2) :
    0 ≤ actualPlainReduction Z D a j := by
  apply Real.logb_nonneg hZ
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))

/-- The actual allocation's formal reduction pays every selected plain factor;
the additional frozen-slot scales can only increase that payment. -/
theorem actual_plain_reduction_le_formal (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (P : ι → ℝ)
    (hP : ∀ i, 1 ≤ P i) :
    (∑ j, actualPlainReduction Z D a j) ≤ Real.logb Z (formalReductionFactor D a P) := by
  have h0 : (0:ℝ) < Ideal.absNorm (selectedPlain D a 0) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0)))
  have h1 : (0:ℝ) < Ideal.absNorm (selectedPlain D a 1) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))
  have hprod : (1:ℝ) ≤ ∏ i∈frozenIndices D a, P i :=
    Finset.one_le_prod₀ (fun i _ => hP i)
  have hnorm := selectedNorm_pos D a
  have hle : selectedNorm D a ≤ formalReductionFactor D a P := by
    unfold formalReductionFactor
    nlinarith
  have hh := Real.logb_le_logb_of_le hZ hnorm hle
  rw [selectedNorm, Real.logb_mul h0.ne' h1.ne'] at hh
  simpa only [Fin.sum_univ_two, actualPlainReduction] using hh

theorem actual_clipped_reduction_nonneg (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (P : ι → ℝ)
    (hP : ∀ i, 1 ≤ P i) (x : Fin 2 → ℝ) :
    0 ≤ clippedReduction (Real.logb Z (formalReductionFactor D a P)) x
      (actualPlainReduction Z D a) :=
  clippedReduction_nonneg _ x _ (actual_plain_reduction_nonneg Z hZ D a)
    (actual_plain_reduction_le_formal Z hZ D a P hP)

/-- Both extraction scalars pay the residual projector's divisor dyad. No
divisibility of that projector into the reconstructed row is required. -/
theorem residual_projector_payment (t theta r₁ r₂ e₁ e₂ omega₁ omega₂ : ℝ)
    (x₁ a₁ x₂ a₂ : Fin 2 → ℝ)
    (hentrance₁ : t ≤ r₁+omega₁) (hentrance₂ : t ≤ r₂+omega₂)
    (herror₁ : |e₁+omega₁| ≤ theta) (herror₂ : |e₂+omega₂| ≤ theta)
    (hclip₁ : negativeTotal (fun i => x₁ i-a₁ i) ≤ theta)
    (hclip₂ : negativeTotal (fun i => x₂ i-a₂ i) ≤ theta) :
    t-(clippedReduction r₁ x₁ a₁+clippedReduction r₂ x₂ a₂)/2+
      (e₁+negativeTotal x₁+e₂+negativeTotal x₂)/2 ≤ 2*theta := by
  have he₁ := (abs_le.mp herror₁).2
  have he₂ := (abs_le.mp herror₂).2
  unfold clippedReduction
  linarith

theorem residual_high_saving (delta r₁ r₂ : ℝ) (hd : 0 ≤ delta)
    (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) : -delta*(r₁+r₂)/2 ≤ 0 := by
  nlinarith [mul_nonneg hd (add_nonneg h₁ h₂)]

theorem signed_rectangle_energy (a b : ℂ) :
    ‖a-b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
  have hn := norm_sub_le a b
  have hs := pow_le_pow_left₀ (norm_nonneg (a-b)) hn 2
  nlinarith [sq_nonneg (‖a‖-‖b‖)]

/-- Split both signed rectangles before attaching any clipped reduction to a
positive term. This is the four-pair Cauchy boundary used by the ledger. -/
theorem signed_rectangle_four_pairs (left right : Fin 2 → ℂ) :
    ‖(left 0-left 1)*star (right 0-right 1)‖^2 ≤
      4*∑ i, ∑ j, ‖left i‖^2*‖right j‖^2 := by
  have hl := signed_rectangle_energy (left 0) (left 1)
  have hr := signed_rectangle_energy (right 0) (right 1)
  have hh := mul_le_mul hl hr (sq_nonneg ‖right 0-right 1‖)
    (show 0 ≤ 2*(‖left 0‖^2+‖left 1‖^2) by positivity)
  rw [norm_mul, norm_star, mul_pow]
  simp only [Fin.sum_univ_two]
  nlinarith [hh]

/-- A finite row energy retains each of the four positive pairs. -/
theorem finite_signed_rectangle_four_pairs {α : Type*} (rows : Finset α)
    (weight : α → ℝ) (hw : ∀ u∈rows, 0 ≤ weight u)
    (left right : α → Fin 2 → ℂ) :
    (∑ u∈rows, weight u*‖(left u 0-left u 1)*star (right u 0-right u 1)‖^2) ≤
      4*∑ i, ∑ j, ∑ u∈rows, weight u*‖left u i‖^2*‖right u j‖^2 := by
  calc
    _ ≤ ∑ u∈rows, weight u*(4*∑ i, ∑ j, ‖left u i‖^2*‖right u j‖^2) :=
      Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left
        (signed_rectangle_four_pairs (left u) (right u)) (hw u hu))
    _ = _ := by
      simp only [Fin.sum_univ_two]
      simp_rw [← Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

end
end Cycle61.Physical

#print axioms Cycle61.Physical.actual_clipped_reduction_nonneg
#print axioms Cycle61.Physical.extraction_scalar_rpow
#print axioms Cycle61.Physical.residual_projector_payment
#print axioms Cycle61.Physical.finite_signed_rectangle_four_pairs

end
/- END ORIGINAL Cycle61.Physical.ClippedProjector -/

/- BEGIN ORIGINAL Cycle61.Physical.AllocationClipping; sha256 8f265791989f5aea6bd22362f9cc714310bda850f48c76a7eb22f80e02c5ef55 -/
section
                                        
                                                             

namespace Cycle61.Physical

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentRetainedEnergy
open CenteredMomentRetainedProfile CenteredMomentActiveDivisorShell
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots
local notation "O" => ActualEisensteinCubic.O

theorem logb_clipped_scale (Z X : ℝ) (hZ : 1 < Z) (hX : 0 < X) :
    Real.logb Z (clippedScale X) = max 0 (Real.logb Z X) := by
  by_cases hx : 1 ≤ X
  · simp only [clippedScale, max_eq_right hx,
      max_eq_right (Real.logb_nonneg hZ hx)]
  · have hx1 : X ≤ 1 := le_of_lt (lt_of_not_ge hx)
    simp only [clippedScale, max_eq_left hx1, Real.logb_one,
      max_eq_left (Real.logb_nonpos hZ hX.le hx1)]

theorem max_positive_sub (x : ℝ) : max 0 x-x = max 0 (-x) := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_right hx, max_eq_left (by linarith : -x ≤ 0)]
    ring
  · rw [max_eq_left (le_of_not_ge hx), max_eq_right (by linarith : 0 ≤ -x)]
    ring

/-- This is the actual change in the two-plain normalizer, including negative
raw lengths. -/
theorem clipping_ratio_log (Z : ℝ) (X : Fin 2 → ℝ) (hZ : 1 < Z)
    (hX : ∀ j, 0 < X j) :
    Real.logb Z ((clippedScale (X 0)*clippedScale (X 1))/(X 0*X 1)) =
      negativeTotal (fun j => Real.logb Z (X j)) := by
  have hc (j : Fin 2) : 0 < clippedScale (X j) :=
    zero_lt_one.trans_le (clippedScale_ge_one _)
  rw [Real.logb_div (mul_pos (hc 0) (hc 1)).ne' (mul_pos (hX 0) (hX 1)).ne',
    Real.logb_mul (hc 0).ne' (hc 1).ne',
    Real.logb_mul (hX 0).ne' (hX 1).ne',
    logb_clipped_scale Z _ hZ (hX 0), logb_clipped_scale Z _ hZ (hX 1)]
  simp only [negativeTotal, Fin.sum_univ_two]
  linarith [max_positive_sub (Real.logb Z (X 0)),
    max_positive_sub (Real.logb Z (X 1))]

theorem clipping_ratio_rpow (Z : ℝ) (X : Fin 2 → ℝ) (hZ : 1 < Z)
    (hX : ∀ j, 0 < X j) :
    Z^(negativeTotal (fun j => Real.logb Z (X j))) =
      (clippedScale (X 0)*clippedScale (X 1))/(X 0*X 1) := by
  rw [← clipping_ratio_log Z X hZ hX]
  exact Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne'
    (div_pos (mul_pos (zero_lt_one.trans_le (clippedScale_ge_one _))
      (zero_lt_one.trans_le (clippedScale_ge_one _))) (mul_pos (hX 0) (hX 1)))

theorem row_sum_support_scale (η : Character) (m A z : O) (W : ℝ → ℂ)
    (t X b : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b)
    (hn : rowTwistedSum η m A z W t X ≠ 0) : 1 ≤ b*X := by
  have hw : ∃ I : Ideal O, I ≠ 0 ∧ W ((Ideal.absNorm I : ℝ)/X) ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    unfold rowTwistedSum
    calc
      _ = ∑' _I : Ideal O, (0 : ℂ) := by
        apply tsum_congr
        intro I
        by_cases hI : I=0
        · subst I
          rw [idealCoeff_zero, zero_mul, zero_mul, zero_mul]
        · rw [h I hI, mul_zero]
      _ = 0 := tsum_zero
  obtain ⟨I,hI,hW⟩ := hw
  have hN : (1 : ℝ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  exact hN.trans ((div_le_iff₀ hX).mp (hs hW))

/-- Nonzero terms, rather than a nominal scale gate, supply the clipping cap. -/
theorem supported_negative_total (Z : ℝ) (X b : Fin 2 → ℝ)
    (hZ : 1 < Z) (hX : ∀ j, 0 < X j) (hs : ∀ j, 1 ≤ b j*X j) :
    negativeTotal (fun j => Real.logb Z (X j)) ≤
      ∑ j, Real.logb Z (max 1 (b j)) := by
  have hj (j : Fin 2) : max 0 (-Real.logb Z (X j)) ≤
      Real.logb Z (max 1 (b j)) := by
    have hB : 0 < max 1 (b j) := zero_lt_one.trans_le (le_max_left _ _)
    have hm : clippedScale (X j) ≤ max 1 (b j)*X j := by
      apply max_le
      · exact (hs j).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hX j).le)
      · simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (b j)) (hX j).le
    have hh := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one _)) hm
    rw [Real.logb_mul hB.ne' (hX j).ne', logb_clipped_scale Z _ hZ (hX j)] at hh
    linarith [max_positive_sub (Real.logb Z (X j))]
  exact Finset.sum_le_sum (fun j _ => hj j)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def postPlainScale (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (j : Fin 2) : ℝ :=
  X j/(Ideal.absNorm (selectedPlain D a j) : ℝ)

theorem postPlainScale_pos (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (j : Fin 2) :
    0 < postPlainScale D a X j := by
  apply div_pos (hX j)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))

theorem postPlainScale_log (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) (j : Fin 2) :
    Real.logb Z (postPlainScale D a X j) =
      Real.logb Z (X j)-actualPlainReduction Z D a j := by
  exact Real.logb_div (hX j).ne' (by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))

theorem actual_post_support (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X : Fin 2 → ℝ) (b₁ b₂ : ℝ)
    (hX : ∀ j, 0 < X j)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hn : allocatedPositiveRow η m A z t S β P D a W₁ W₂ (X 0) (X 1) ≠ 0) :
    1 ≤ b₁*postPlainScale D a X 0 ∧ 1 ≤ b₂*postPlainScale D a X 1 := by
  unfold allocatedPositiveRow retainedPositiveRow positiveSlotRow at hn
  have hp := left_ne_zero_of_mul (right_ne_zero_of_mul hn)
  have h₁ : rowTwistedSum η m A z W₁ t (postPlainScale D a X 0) ≠ 0 := by
    rw [clipped_rowTwistedSum η m A z W₁ t _ (postPlainScale_pos D a X hX 0)]
    exact left_ne_zero_of_mul hp
  have h₂ : rowTwistedSum η m A z W₂ t (postPlainScale D a X 1) ≠ 0 := by
    rw [clipped_rowTwistedSum η m A z W₂ t _ (postPlainScale_pos D a X hX 1)]
    exact right_ne_zero_of_mul hp
  exact ⟨row_sum_support_scale η m A z W₁ t _ b₁
    (postPlainScale_pos D a X hX 0) hs₁ h₁,
    row_sum_support_scale η m A z W₂ t _ b₂
      (postPlainScale_pos D a X hX 1) hs₂ h₂⟩

theorem actual_post_clipping_bound (Z : ℝ) (hZ : 1 < Z)
    (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X b : Fin 2 → ℝ) (hX : ∀ j, 0 < X j)
    (hs₁ : Function.support W₁ ⊆ Set.Iic (b 0))
    (hs₂ : Function.support W₂ ⊆ Set.Iic (b 1))
    (hn : allocatedPositiveRow η m A z t S β P D a W₁ W₂ (X 0) (X 1) ≠ 0) :
    negativeTotal (fun j => Real.logb Z (X j)-actualPlainReduction Z D a j) ≤
      ∑ j, Real.logb Z (max 1 (b j)) := by
  have hh := actual_post_support η m A z t S β P D a W₁ W₂ X (b 0) (b 1)
    hX hs₁ hs₂ hn
  have hs : ∀ j : Fin 2, 1 ≤ b j*postPlainScale D a X j := by
    intro j
    fin_cases j
    · exact hh.1
    · exact hh.2
  simpa only [postPlainScale_log Z D a X hX] using
    supported_negative_total Z (postPlainScale D a X) b hZ
      (postPlainScale_pos D a X hX) hs

/-- The scalar is the literal change in the actual normalizer; no new
coprimality condition is attached to either plain quotient. -/
theorem actual_clipped_scalar_squared (Z : ℝ) (hZ : 1 < Z)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ) (hP : ∀ i, 0 < P i) (X : Fin 2 → ℝ) (hX : ∀ j, 0 < X j) :
    Z^(-clippedReduction (Real.logb Z (formalReductionFactor D a P))
        (fun j => Real.logb Z (X j)) (actualPlainReduction Z D a)+
      negativeTotal (fun j => Real.logb Z (X j))) =
      ((clippedScale (postPlainScale D a X 0)*clippedScale (postPlainScale D a X 1))/
        (postPlainScale D a X 0*postPlainScale D a X 1))/formalReductionFactor D a P := by
  have hF : 0 < formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _ => hP i))
  have hz : 0 < Z := zero_lt_one.trans hZ
  have he : -clippedReduction (Real.logb Z (formalReductionFactor D a P))
      (fun j => Real.logb Z (X j)) (actualPlainReduction Z D a)+
      negativeTotal (fun j => Real.logb Z (X j)) =
      -Real.logb Z (formalReductionFactor D a P)+
        negativeTotal (fun j => Real.logb Z (postPlainScale D a X j)) := by
    simp only [postPlainScale_log Z D a X hX, clippedReduction]
    ring
  rw [he, Real.rpow_add hz, Real.rpow_neg hz.le,
    Real.rpow_logb hz hZ.ne' hF,
    clipping_ratio_rpow Z _ hZ (postPlainScale_pos D a X hX)]
  ring

end
end Cycle61.Physical

#print axioms Cycle61.Physical.actual_post_clipping_bound
#print axioms Cycle61.Physical.actual_clipped_scalar_squared

end
/- END ORIGINAL Cycle61.Physical.AllocationClipping -/
