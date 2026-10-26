import Candidate.Cycle63.Physical.InitialMass.GeometryAdmission

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle63InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum
open CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
open CenteredMomentLogDyadic CenteredMomentPrimeElements CenteredMomentPrimePool
open CenteredMomentEnergyFirstAnnularAdmission CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationRadicalChoice
open CenteredMomentSecondHeightFamily RayFourExpansion
open CenteredMomentChildRows CenteredMomentAmplificationActiveFactor CenteredMomentFirstAmplificationChoice
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance geometryAmplificationDecidableSum : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def geometryAllocationWeight (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) : ℝ :=
  let C := geometryColumnIdeal reflected s R seed K Z ξ hK key j
  if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
    ‖geometryColumnScalar reflected s R seed K Z ξ M A hK key weight j‖^2*
      ((max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/C.absNorm)*(frozenControl B.val s.M)^2
  else 0

omit [DecidableEq ι] in
lemma geometryAllocationWeight_nonneg (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b : ℝ)
    (j : FirstColumnIndex (geometryFirstSource s R seed K Z ξ hK key))
    (B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j)) :
    0≤geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B := by
  unfold geometryAllocationWeight
  dsimp only
  split_ifs <;> positivity

omit [DecidableEq ι] in
/-- Exact allocation sum underlying the first-source budget. Zero frozen
coefficients remain zero weights, before applying amplification. -/
theorem geometryLiveBudget_eq_allocations (reflected : Bool) (s : Input ι) (R seed : Ideal O)
    (K Z ξ M A : ℝ) (hK : 0<K) (key : ℤ×(Fin 5→ℤ))
    (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (b t : ℝ) :
    geometryLiveBudget reflected s R seed K Z ξ M A hK key weight N b t=
    ∑j : firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus),
      ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val),
        geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val B*
          childNormalizedGaussSource s (geometryColumnIdeal reflected s R seed K Z ξ hK key j.val)
            R j.val.2.1.val B (geometryColumnCharacter reflected s R seed K Z ξ hK key j.val)
              t CenteredMomentFirstAnnularMajorant.profile
              (geometryFirstSource s R seed K Z ξ hK key j.val.1).H0 := by
  rw [Finset.sum_coe_sort _ (fun j=>
    ∑B : actualAllocations s.pools (geometryColumnIdeal reflected s R seed K Z ξ hK key j),
      geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j B*
        childNormalizedGaussSource s (geometryColumnIdeal reflected s R seed K Z ξ hK key j)
          R j.2.1.val B (geometryColumnCharacter reflected s R seed K Z ξ hK key j)
            t CenteredMomentFirstAnnularMajorant.profile
            (geometryFirstSource s R seed K Z ξ hK key j.1).H0)]
  dsimp only [geometryLiveBudget]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun B hB => ?_
  unfold geometryAllocationWeight
  dsimp only
  split_ifs <;> ring

omit [DecidableEq ι] in
/-- Amplification of the literal, unreflected or reflected first-source
budget. All first columns and common allocations stay in the same sum. -/
theorem actual_geometry_budget_amplification
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Amax D ξcap Bcap b eta ξ reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hcap : 0≤amplifierCap Amax D ξcap)
    (hb : 0≤b) (hgap : eta<sigma/6) (hξ : 0≤ξ) (hξcap : ξ≤ξcap)
    (hreserve : 0< reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀(reflected : Bool) (s : Input ι) (R seed : Ideal O) (K M A : ℝ) (hK : 0<K)
      (key : ℤ×(Fin 5→ℤ))
      (weight : Cycle63JointSource.SourceCoordinate s R seed K Z ξ→ℂ) (N : ℕ) (t : ℝ),
      CenteredMomentExceptionalAmplitudePair.volume s.toData≤Z^Amax → K⁻¹≤Z^D →
      R≠0 → (R.absNorm:ℝ)≤Z^BR → Squarefree seed → s.W₁ 0=0 → s.W₂ 0=0 →
      sourceRadius s≤Z^Bcap →
      (∀I∈finiteColumns (Fintype.piFinset s.pools),(I.absNorm:ℝ)≤Z^Bs) →
      (∀i,Function.support (s.W i)⊆Set.Iic b) →
    ∀z : ι→ℝ, (∀i,z i≤eta) → (∀i,s.P i=Z^(z i)) →
    let Label := ↥(firstLiveColumns (geometryFirstSource s R seed K Z ξ hK key) (fun _=>logAnnulus));
    let C (j : Label) := geometryColumnIdeal reflected s R seed K Z ξ hK key j.val;
    let χ (j : Label) := geometryColumnCharacter reflected s R seed K Z ξ hK key j.val;
    let g (j : Label) := geometryBranch reflected s R seed K Z ξ hK key j.val;
    let w (j : Label) := geometryAllocationWeight reflected s R seed K Z ξ M A hK key weight N b j.val;
    ∃τ : (j : Label)→actualAllocations s.pools (C j)→elementPool P→Fin 3→RayCharacter→ Character,
      (∀j B p i ψ,(τ j B p i ψ).modulus.absNorm≤
        radicalBound (childCharacter (χ j) ψ) fixedBadMask p.val
          (errorMovingExponent (errorIndex i))) ∧
      geometryLiveBudget reflected s R seed K Z ξ M A hK key weight N b t ≤
      (56/(P.card:ℝ))*
        (((amplifierCap Amax D ξcap+2*sigma)/(sigma/6))*
          (∑j,∑B,w j B*actualMainSource (child s (C j) R B (χ j) t)
            (g j) Z sigma 1 ξ reserve)+
          ∑j,∑B,w j B*actualErrorSources (child s (C j) R B (χ j) t)
            (g j) Z sigma 1 ξ reserve P (τ j B)) := by
  filter_upwards [eventually_ge_atTop (32:ℝ),
    actual_common_children_amplification (ι:=ι) rayM H hH Sbad hbad
      sigma loss (BR+Bcap) Bs (amplifierCap Amax D ξcap) b eta 1 ξ reserve
      hsigma hloss hcap hb hgap le_rfl hξ hreserve] with Z hZ hz
  refine ⟨hz.1,hz.2.1,hz.2.2.1,?_⟩
  intro reflected s R seed K M A hK key weight N t hV hKi hR hRn hs hz₁ hz₂
    hsource hpool hsupp z hzslot hlen Label C χ g w
  obtain ⟨τ,hτ,he⟩ := hz.2.2.2 s R C g χ (fun _=>t) w
    (fun j B=>geometryAllocationWeight_nonneg reflected s R seed K Z ξ M A hK key weight N b j.val B)
    (fun _=>rfl)
    (fun j=>actual_geometry_admission reflected s R seed K Z ξ Amax D ξcap Bcap BR Bs hK hZ
      hξcap hV hKi hR hRn hs hz₁ hz₂ hsource hpool key j.val)
    hsupp z hzslot hlen
  refine ⟨τ,hτ,?_⟩
  rw [geometryLiveBudget_eq_allocations]
  exact he

end
end OAI.SevenEighths.Cycle63InitialMass
