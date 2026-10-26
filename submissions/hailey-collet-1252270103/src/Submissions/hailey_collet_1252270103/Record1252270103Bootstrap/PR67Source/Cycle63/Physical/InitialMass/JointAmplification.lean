import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.InitialMass.Decomposition
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
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
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec ξ reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b)
    (hgap : eta<sigma/6) (hC : 1≤Csec) (hξ : 0≤ξ) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀{Label : Type*} [Fintype Label],
    ∀slots : Label→Finset ι, ∀s : (j : Label)→ Input (slots j), ∀g : Label→FirstBranchGeometry, ∀weight : Label→ℝ,
      (∀j,0≤weight j) → (∀j,g j |>.Eligible Z BR Bs Mmax Csec ξ) →
      (∀j,∀i,Function.support ((s j).W i)⊆Set.Iic b) →
    ∀z : (j : Label)→slots j→ℝ, (∀j i,z j i≤eta) → (∀j i,(s j).P i=Z^(z j i)) →
    ∃τ : Label→elementPool P→Fin 3→RayCharacter→ Character,
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
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec ξ reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b)
    (hgap : eta<sigma/6) (hC : 1≤Csec) (hξ : 0≤ξ) (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀{Label : Type*} [Fintype Label], ∀s : Input ι, ∀R : Ideal O,
    ∀C : Label→ Ideal O, ∀g : Label→FirstBranchGeometry, ∀χ : Label→ Character,
    ∀t : Label→ℝ, ∀weight : (j : Label)→actualAllocations s.pools (C j)→ℝ,
      (∀j B,0≤weight j B) → (∀j,(g j).R=R*C j) →
      (∀j,(g j).Eligible Z BR Bs Mmax Csec ξ) →
      (∀i,Function.support (s.W i)⊆Set.Iic b) →
    ∀z : ι→ℝ, (∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
    ∃τ : (j : Label)→actualAllocations s.pools (C j)→elementPool P→Fin 3→RayCharacter→ Character,
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
end OAI.SevenEighths.Cycle63InitialMass

end Record1252270103Bootstrap.PR67
