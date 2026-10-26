import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Cycle61.Physical.InitialMass.SecondActive

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondSectorColumns CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondCanonicalScalar CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O

abbrev SecondBlockSource.LeftIndex (s : SecondBlockSource) := sectorPool s.C s.hC.1 s.pool
abbrev SecondBlockSource.RightIndex (s : SecondBlockSource) := sectorPool s.D s.hD.1 s.pool
abbrev SecondSector {Label : Type*} (s : Label→SecondBlockSource) :=
  (l : Label) × (_L : ↥(s l).divisors) × RayCharacter × RayCharacter × ↥(s l).rows

def SecondBlockSource.outside (s : SecondBlockSource) : ℝ :=
  outerScalar s.C s.D s.K s.dyad*normalizer s.C s.D s.inactive
def SecondBlockSource.value (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ)) : ℂ :=
  physicalBlock s.character s.height s.pool s.beta s.C s.D s.hC s.hD s.inactive
    s.radius s.rows W s.K s.dyad
def secondJointSource {Label : Type*} (s : Label→SecondBlockSource) (q : SecondSector s) :=
  (s q.1).sector q.2.1.val q.2.2.1 q.2.2.2.1
def secondJointWeight {Label : Type*} (s : Label→SecondBlockSource) (q : SecondSector s) : ℂ :=
  (secondJointSource s q).signedWeight ((s q.1).rowWeight q.2.2.2.2.val)
def secondJointLeft {Label : Type*} (s : Label→SecondBlockSource) (w : Label→ℂ)
    (q : SecondSector s) (i : (s q.1).LeftIndex) : ℂ :=
  w q.1*(s q.1).outside*(secondJointSource s q).leftCoefficient i*idealRowHom q.2.2.2.2.val i
def secondJointRight {Label : Type*} (s : Label→SecondBlockSource)
    (q : SecondSector s) (i : (s q.1).RightIndex) : ℂ :=
  (secondJointSource s q).rightCoefficient i*idealRowHom (-q.2.2.2.2.val) i
def secondLeftLog (s : SecondBlockSource) (i : s.LeftIndex) :=
  Real.log ((i.val.absNorm:ℝ)/CenteredMomentSectorLocalization.dyadicScale (s.dyad 2))
def secondRightLog (s : SecondBlockSource) (i : s.RightIndex) :=
  Real.log ((i.val.absNorm:ℝ)/CenteredMomentSectorLocalization.dyadicScale (s.dyad 3))

/-- The literal weighted physical blocks expand over one joint coordinate,
with no supremum or independent charge for their original source labels. -/
theorem actual_second_batch_expression {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=
      ∑q : SecondSector s,secondJointWeight s q*
        ∑i : (s q.1).LeftIndex,∑j : (s q.1).RightIndex,
          (secondJointLeft s w q i*star (secondJointRight s q j))*
            wholeKernel W (fun _=>logAnnulus) (s q.1).ratio (s q.1).rho
              ((s q.1).x q.2.2.2.2.val) (secondLeftLog (s q.1) i) (secondRightLog (s q.1) j) := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro l hl
  rw [SecondBlockSource.value,actual_second_physical_block_expression]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type,Finset.mul_sum]
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro z hz
  simp only [secondSectorTerm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [secondJointWeight,secondJointLeft,secondJointRight,secondJointSource,
    SecondBlockSource.outside,Complex.ofReal_mul,secondLeftLog,secondRightLog,
    CanonicalSectorSource.leftLog,CanonicalSectorSource.rightLog,SecondBlockSource.sector]
  ring

def secondActiveSectors {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) : Finset (SecondSector s) :=
  Finset.univ.filter (fun q=>logAnnulus (s q.1).rho≠0 ∧
    logAnnulus ((s q.1).x q.2.2.2.2.val)≠0 ∧ Squarefree q.2.1.val ∧
    (s q.1).rowWeight q.2.2.2.2.val≠0)

theorem actual_second_batch_active_expression {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (w : Label→ℂ) (W : 𝓢(ℝ,ℂ)) :
    (∑l,w l*(s l).value W)=
      ∑q∈secondActiveSectors s,secondJointWeight s q*
        ∑i : (s q.1).LeftIndex,∑j : (s q.1).RightIndex,
          (secondJointLeft s w q i*star (secondJointRight s q j))*
            wholeKernel W (fun _=>logAnnulus) (s q.1).ratio (s q.1).rho
              ((s q.1).x q.2.2.2.2.val) (secondLeftLog (s q.1) i) (secondRightLog (s q.1) j) := by
  rw [actual_second_batch_expression,secondActiveSectors,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases h₀ : logAnnulus (s q.1).rho=0
  · simp [h₀,wholeKernel]
  · by_cases h₁ : logAnnulus ((s q.1).x q.2.2.2.2.val)=0
    · simp [h₁,wholeKernel]
    · by_cases hL : Squarefree q.2.1.val
      · by_cases hw : (s q.1).rowWeight q.2.2.2.2.val=0
        · simp [hw,secondJointWeight,CanonicalSectorSource.signedWeight]
        · simp [h₀,h₁,hL,hw]
      · simp [h₀,h₁,hL,secondJointWeight,secondJointSource,SecondBlockSource.sector,
          CanonicalSectorSource.signedWeight]

def secondActiveEnergyPair {Label : Type*} [Fintype Label]
    (s : Label→SecondBlockSource) (w : Label→ℂ) (t : ℝ) : ℝ :=
  Real.sqrt (∑q∈secondActiveSectors s,
    ‖leftColumn Finset.univ (secondJointLeft s w q) logAnnulus (secondLeftLog (s q.1)) t‖^2)*
  Real.sqrt (∑q∈secondActiveSectors s,
    ‖rightColumn Finset.univ (secondJointRight s q) logAnnulus (secondRightLog (s q.1)) t‖^2)

theorem actual_second_batch_contraction (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀{Label : Type*}[Fintype Label][DecidableEq Label]
      (s : Label→SecondBlockSource) (w : Label→ℂ) (r : ℝ),
      0<r → (∀l,(s l).ratio=r) → ∀E : ℝ,0≤E →
      (∀t : ℝ,secondActiveEnergyPair s w t≤E*(1+‖t‖)^J) →
        (1+r)^A*‖∑l,w l*(s l).value W‖≤C*E := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_dependent_row_estimate W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ _ hn=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro Label _ _ s w r hr heq E hE he
  rw [actual_second_batch_active_expression]
  simp_rw [heq]
  exact hbound r hr (Label:=Label) (κ:=SecondSector s)
    (α:=fun l=>(s l).LeftIndex) (β:=fun l=>(s l).RightIndex)
    (secondActiveSectors s) (fun q=>q.1) (secondJointLeft s w) (secondJointRight s)
    (fun l=>secondLeftLog (s l)) (fun l=>secondRightLog (s l))
    (fun q=>(s q.1).rho) (fun q=>(s q.1).x q.2.2.2.2.val) (secondJointWeight s)
    (fun q _=>canonical_sector_signed_weight_norm _ _ (actual_second_row_weight_norm _ _))
    (fun _ _=>logAnnulus_norm _) (fun _ _=>logAnnulus_norm _) E hE he

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_batch_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_batch_active_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_batch_contraction
