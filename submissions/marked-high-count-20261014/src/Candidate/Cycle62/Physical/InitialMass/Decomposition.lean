import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstAnnularInputAmplification
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstCommonSourceBudget
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.FirstReferenceSource
import Lean

set_option autoImplicit false
set_option maxHeartbeats 0
namespace OAI.SevenEighths.Cycle62InitialMass
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
open CenteredMomentChildRows RayFourExpansion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- Exact physical source mass, with all first labels, inactive subsets and
local dyadic blocks retained. There is no first-label counting envelope. -/
theorem actual_physical_mass_direct_sum (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (fixedBadMask*idealGenerator R) 1 W K Z ξ =
      ∑p : Labels s R seed, ∑E∈inactiveSubsets p.val.1 p.val.2,
        ∑n : SourceBlocks s R seed K Z ξ p E,
          ‖originalBlock s R seed W K Z ξ p E n‖ :=
  physicalMass_eq_sum s R seed W K Z ξ

/-- The physical source's complete coordinate, including every first label,
inactive subset and local dyadic block. -/
abbrev FirstSourceCoordinate (s : Input ι) (R seed : Ideal O) (K Z ξ : ℝ) :=
  (p : Labels s R seed) ×
    (E : ↥(inactiveSubsets p.val.1 p.val.2)) × SourceBlocks s R seed K Z ξ p E.val

def coordinateBlock (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ))
    (K Z ξ : ℝ) (q : FirstSourceCoordinate s R seed K Z ξ) : ℂ :=
  originalBlock s R seed W K Z ξ q.1 q.2.1.val q.2.2

/-- A harmless unit phase converts the literal sum of block norms into one
joint complex sum, retaining its full coordinate. -/
def normPhase (z : ℂ) : ℂ := (‖z‖ : ℂ)/z

lemma normPhase_norm (z : ℂ) : ‖normPhase z‖≤1 := by
  by_cases hz : z=0
  · simp [normPhase,hz]
  · simp [normPhase,norm_ne_zero_iff.mpr hz]

lemma normPhase_mul (z : ℂ) : normPhase z*z=(‖z‖ : ℂ) := by
  by_cases hz : z=0
  · simp [normPhase,hz]
  · exact div_mul_cancel₀ _ hz

/-- Exact joint first-source representation. These phases have norm at most
one, so joint Mellin/sector contraction can consume the whole physical mass
without introducing a count of first labels. -/
theorem actual_physical_mass_joint_sum (s : Input ι) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) :
    physicalMass s R seed (fixedBadMask*idealGenerator R) 1 W K Z ξ =
      ‖∑q : FirstSourceCoordinate s R seed K Z ξ,
        normPhase (coordinateBlock s R seed W K Z ξ q)*
          coordinateBlock s R seed W K Z ξ q‖ := by
  simp_rw [normPhase_mul]
  rw [←Complex.ofReal_sum]
  rw [Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  rw [actual_physical_mass_direct_sum,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _
  rw [Fintype.sum_sigma]
  dsimp only [coordinateBlock]
  exact (Finset.sum_coe_sort (inactiveSubsets p.val.1 p.val.2)
    (fun E => ∑n : SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖)).symm

omit [DecidableEq ι] in
/-- Literal allocation reduction over the entire matched common-label family.
All live allocation coefficients and child normalizers remain visible. -/
theorem actual_common_allocation_direct_sum {Label : Type*} [Fintype Label]
    (N : ℕ) (a b : ℝ) (ha : 0<a) (s : Input ι)
    (hcard : Fintype.card ι≤N) (haS : a≤s.lower) (hbS : s.upper≤b)
    (C : Label→Ideal O) (R seed : Ideal O) (hC : ∀j,Supported (C j))
    (hseed : ∀j,seed∣C j) (τ : Label→Character) (t : Label→ℝ)
    (L : Label→Ideal O) (W : 𝓢(ℝ,ℂ)) (K weight : Label→ℝ)
    (hK : ∀j,0<K j) (hw : ∀j,0≤weight j)
    (hW : ∀j,∀z : O,0≤(W (‖eisEmbedding z‖^2/K j)).re) :
    (∑j,weight j*((CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) (C j) (hC j)
      (τ j) (t j) (L j) W (K j)).re/volume s)) ≤
    ∑j,weight j*((max 1 b)^N*((actualAllocations s.pools (C j)).card:ℝ)/(C j).absNorm*
      ∑B : actualAllocations s.pools (C j),
        if frozenCoefficient B.val (C j) R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s (C j) R (L j) B
            (τ j) (t j) W (K j)
        else 0) := by
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left
    (common_energy_live_allocations N a b ha s hcard haS hbS (C j) R seed
      (hC j) (hseed j) (τ j) (t j) (L j) W (K j) (hK j) (hW j)) (hw j)

/-- Geometric data of a literal amplified source branch. -/
structure FirstBranchGeometry where
  (R seed I J E : Ideal O)
  (d cLog K X Tsec H0 : ℝ)

def FirstBranchGeometry.Eligible (g : FirstBranchGeometry) (Z BR Bs Mmax Csec ξ : ℝ) : Prop :=
  g.R≠0 ∧ g.seed≠0 ∧ (g.R.absNorm:ℝ)≤Z^BR ∧ (g.seed.absNorm:ℝ)≤Z^Bs ∧
  g.E≠0 ∧ 0<g.K ∧ 0<g.X ∧ g.Tsec≤Csec*firstNominalScale g.I g.J g.E g.K g.X ∧
  0<g.H0 ∧ g.H0≤4*frequencyRadius g.Tsec Z ξ ∧ 8*g.H0≤Z^Mmax

def actualMainSource (s : Input ι) (g : FirstBranchGeometry)
    (Z sigma Csec ξ reserve : ℝ) : ℝ :=
  normalizedGaussSource s g.R g.seed ballProfile
    (mainCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z) g.cLog sigma
      (frequencyLoss Z (32*Csec) ξ) reserve)

def actualErrorSources (s : Input ι) (g : FirstBranchGeometry)
    (Z sigma Csec ξ reserve : ℝ) (P : Finset (Ideal O))
    (τ : elementPool P→Fin 3→RayCharacter→Character) : ℝ :=
  ∑p : elementPool P, ∑i : Fin 3,
    (16*(errorIndex i+2:ℝ)*localErrorCost p (errorIndex i))*
      ∑χ : RayCharacter, ∑B : actualAllocations (activeInput s).pools
          ((Ideal.span {p.val})^(errorIndex i+1)),
        childNormalizedGaussSource (activeInput s) ((Ideal.span {p.val})^(errorIndex i+1))
          g.R g.seed B (τ p i χ) s.t ballProfile
          (errorCommonRadius Z g.d (nominalLog g.I g.J g.E g.K g.X Z) g.cLog sigma
            (frequencyLoss Z (32*Csec) ξ) reserve p (errorIndex i+1))

omit [DecidableEq ι] in
/-- Genuine source amplification in the full matched direct sum. The same
prime pool and threshold work before the live family. No first-label envelope
or terminal energy estimate is assumed. The three extracted branches remain
literal child sources, with their local error costs and allocation normalizers. -/
theorem actual_matched_source_amplification
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta Csec ξ reserve : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b)
    (hgap : eta<sigma/6) (hC : 1≤Csec) (hξ : 0≤ξ) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := CenteredMomentPrimePool.primePool rayM H Sbad (1/2) 1 (Z^(sigma/3));
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
    ∀{Label : Type*} [Fintype Label],
    ∀s : Label→Input ι, ∀g : Label→FirstBranchGeometry, ∀weight : Label→ℝ,
      (∀j,0≤weight j) → (∀j,g j |>.Eligible Z BR Bs Mmax Csec ξ) →
      (∀j,∀i,Function.support ((s j).W i)⊆Set.Iic b) →
    ∀z : Label→ι→ℝ, (∀j i,z j i≤eta) → (∀j i,(s j).P i=Z^(z j i)) →
    ∃τ : Label→elementPool P→Fin 3→RayCharacter→Character,
      (∀j p i χ,(τ j p i χ).modulus.absNorm≤
        radicalBound (childCharacter (s j).η χ) fixedBadMask p.val
          (errorMovingExponent (errorIndex i))) ∧
      (∑j,weight j*normalizedGaussSource (s j) (g j).R (g j).seed
        CenteredMomentFirstAnnularMajorant.profile (g j).H0) ≤
      (56/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*(∑j,weight j*actualMainSource (s j) (g j) Z sigma Csec ξ reserve)+
          ∑j,weight j*actualErrorSources (s j) (g j) Z sigma Csec ξ reserve P (τ j)) := by
  filter_upwards [eventually_input_amplification (ι:=ι) rayM H hH Sbad hbad
    sigma loss BR Bs Mmax b eta Csec ξ reserve hsigma hloss hM hb hgap hC hξ hreserve] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro Label _ s g weight hw hg hsupp z hz hlen
  choose τ hN henergy using (fun j => hfam (s j).η)
  refine ⟨τ,hN,?_⟩
  have hbranch (j : Label) := henergy j (s j) rfl (hsupp j) (z j) (hz j) (hlen j)
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

end
end OAI.SevenEighths.Cycle62InitialMass
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_physical_mass_direct_sum
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_physical_mass_joint_sum
#print axioms OAI.SevenEighths.Cycle62InitialMass.normPhase_norm
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_common_allocation_direct_sum
#print axioms OAI.SevenEighths.Cycle62InitialMass.actual_matched_source_amplification

open Lean in
run_cmd do
  let env := (← getEnv).setExporting false
  for (root, required) in #[
      (``OAI.SevenEighths.Cycle62InitialMass.actual_physical_mass_direct_sum,
        ``OAI.SevenEighths.CenteredMomentFirstReferenceSource.physicalMass_eq_sum),
      (``OAI.SevenEighths.Cycle62InitialMass.actual_physical_mass_joint_sum,
        ``OAI.SevenEighths.CenteredMomentFirstReferenceSource.physicalMass_eq_sum),
      (``OAI.SevenEighths.Cycle62InitialMass.actual_common_allocation_direct_sum,
        ``OAI.SevenEighths.CenteredMomentFirstCommonSourceBudget.common_energy_live_allocations),
      (``OAI.SevenEighths.Cycle62InitialMass.actual_matched_source_amplification,
        ``OAI.SevenEighths.CenteredMomentFirstAnnularInput.eventually_input_amplification)] do
    let mut todo : Array Name := #[root]
    let mut seen : NameSet := {}
    let mut idx := 0
    let mut denied : Array Name := #[]
    let mut missing : Array Name := #[]
    while idx < todo.size do
      let n := todo[idx]!
      idx := idx+1
      if seen.contains n then continue
      seen := seen.insert n
      if n == ``sorryAx || #["ColumnBounds", "actual_reference_block", "original_block_sum",
          "CenteredMomentEnergyOriginalHighReflectionPower", "Cycle62Moment.InitialAffineAt",
          "Cycle62.Assembly.Final", "PositiveHighSourceBound"].any
          (fun ban => (n.toString.splitOn ban).length>1) then
        denied := denied.push n
      match env.find? n with
      | none => missing := missing.push n
      | some ci =>
        for dep in ci.getUsedConstantsAsSet.toArray do
          if #["OAI.", "Cycle25.", "Cycle62.", "ZetaZeroFree.",
              "_private.OAI.", "_private.Cycle25.", "_private.Cycle62.",
              "_private.ZetaZeroFree."].any (fun p => dep.toString.startsWith p) then
            todo := todo.push dep
    unless seen.contains required do throwError "Genuine source dependency missing: {required}"
    logInfo m!"{root}: {seen.size} project constants; denied={denied}; missing={missing}"
    unless denied.isEmpty && missing.isEmpty do throwError "Direct-sum decomposition audit rejected"
