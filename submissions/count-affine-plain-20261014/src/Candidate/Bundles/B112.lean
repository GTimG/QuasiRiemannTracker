/- Packaging rehearsal. Original notices retained; separate replay required. -/
import Candidate.Bundles.B111
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.CommonSectorWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondPhysicalBlock

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondBlock; sha256 02e58031d3d44ffff51bae9e85cd18ef4968c16a5982823336d553ed48a60c42 -/
section
                                       
                                       
                                                              

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondSectorChildren
open CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondPhysicalBlock
open CenteredMomentSecondPhysicalWindow CenteredMomentSecondWholeKernel
open CenteredMomentSecondRadicalBlock CenteredMomentSectorLocalization
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentMobiusRegroup CenteredMomentChildAssembly CenteredMomentFixedRay
open CenteredMomentSecondScaled CenteredMomentSourceRow Cycle61Moment RayFourExpansion
open CenteredMomentSupport CenteredMomentCauchy
local notation "O" => HeckeFamily.O

/-- Literal retained second-block data. The canonical partition remains
inside its signed weight throughout the joint expansion. -/
structure SecondBlockSource where
  character : Character
  height : ℝ
  pool : Finset (Ideal O)
  beta : Ideal O→ℂ
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  sameSupport : primeSupport C=primeSupport D
  inactive : Finset (CommonIndex C D)
  radius : ℝ
  rows : Finset O
  rows_ne : ∀z∈rows,z≠0
  K : ℝ
  K_pos : 0< K
  dyad : Fin 4→ℤ

def SecondBlockSource.frequency (s : SecondBlockSource) :=
  commonFrequencyGenerator s.C s.D*nonunitFrequencyGenerator s.C s.D s.inactive
abbrev SecondBlockSource.divisors (s : SecondBlockSource) :=
  divisorPool Finset.univ (fun J : sectorPool s.D s.hD.1 s.pool=>(J:Ideal O))
def SecondBlockSource.ratio (s : SecondBlockSource) :=
  dyadicScale (s.dyad 0)*dyadicScale (s.dyad 1)/(dyadicScale (s.dyad 2)*dyadicScale (s.dyad 3))
def SecondBlockSource.rho (s : SecondBlockSource) :=
  Real.log (secondEffectiveScale s.C s.D s.frequency s.K/dyadicScale (s.dyad 0))
def SecondBlockSource.x (s : SecondBlockSource) (z : O) :=
  Real.log (normValue z/dyadicScale (s.dyad 1))
def SecondBlockSource.rowWeight (s : SecondBlockSource) (z : O) :=
  retainedScalar s.C s.D s.inactive s.radius z*idealCorrelation s.C s.D s.hC s.hD (s.frequency*z)

def SecondBlockSource.sector (s : SecondBlockSource) (L : Ideal O) (χ ψ : RayCharacter) :
    CanonicalSectorSource where
  C := s.C
  D := s.D
  supportedC := s.hC
  supportedD := s.hD
  sameSupport := s.sameSupport
  pool := s.pool
  coefficient := s.beta
  character := s.character
  height := s.height
  frequency := s.frequency
  projector := L
  leftRay := χ
  rightRay := ψ
  leftScale := dyadicScale (s.dyad 2)
  rightScale := dyadicScale (s.dyad 3)

def secondSectorTerm (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ))
    (L : Ideal O) (χ ψ : RayCharacter) (z : O) : ℂ :=
  let src := s.sector L χ ψ
  src.signedWeight (s.rowWeight z)*
    ∑I : src.LeftIndex,∑J : src.RightIndex,
      ((src.leftCoefficient I*idealRowHom z I)*star (src.rightCoefficient J*idealRowHom (-z) J))*
        wholeKernel W (fun _=>logAnnulus) s.ratio s.rho (s.x z) (src.leftLog I) (src.rightLog J)

/-- Exact second-transform expansion, before any Cauchy inequality,
absolute values or estimates of individual source labels. -/
theorem actual_second_block_expression (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ)) :
    normalizedBlock s.character s.height s.pool s.beta s.C s.D s.hC s.hD s.inactive
      s.radius s.rows W s.K s.dyad=
      ∑L∈s.divisors,∑χ : RayCharacter,∑ψ : RayCharacter,∑z∈s.rows,
        secondSectorTerm s W L χ ψ z := by
  have he := sector_correlation_children s.character s.height s.pool s.beta s.C s.D s.hC s.hD
    s.sameSupport s.frequency s.rows
    (retainedScalar s.C s.D s.inactive s.radius)
    (fun z I J=>wholeKernel W (fun _=>logAnnulus) s.ratio s.rho (s.x z)
      (Real.log ((I.absNorm:ℝ)/dyadicScale (s.dyad 2)))
      (Real.log ((J.absNorm:ℝ)/dyadicScale (s.dyad 3))))
  apply he.trans
  simp only [Finset.mul_sum,secondSectorTerm,SecondBlockSource.sector,
    CanonicalSectorSource.signedWeight,CanonicalSectorSource.leftCoefficient,
    CanonicalSectorSource.rightCoefficient,CanonicalSectorSource.leftLog,
    CanonicalSectorSource.rightLog,SecondBlockSource.rowWeight]
  apply Finset.sum_congr rfl
  intro L hL
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro ψ hψ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  ring

theorem actual_second_physical_block_expression (s : SecondBlockSource) (W : 𝓢(ℝ,ℂ)) :
    physicalBlock s.character s.height s.pool s.beta s.C s.D s.hC s.hD s.inactive
      s.radius s.rows W s.K s.dyad=
      (outerScalar s.C s.D s.K s.dyad:ℂ)*(normalizer s.C s.D s.inactive:ℂ)*
        ∑L∈s.divisors,∑χ : RayCharacter,∑ψ : RayCharacter,∑z∈s.rows,
          secondSectorTerm s W L χ ψ z := by
  rw [physicalBlock_eq _ _ _ _ _ _ _ _ _ _ _ s.rows_ne _ _ s.K_pos,
    actual_second_block_expression]

theorem actual_second_row_weight_norm (s : SecondBlockSource) (z : O) :
    ‖s.rowWeight z‖≤1 :=
  actual_retained_scalar_norm s.C s.D s.hC s.hD s.sameSupport s.inactive s.radius z

/-- The literal second-sector terms, jointly over all source labels and
rows in one ratio group. Scalar factors stay inside their column energies. -/
theorem actual_joint_second_block_bound (W : 𝓢(ℝ,ℂ)) (A J : ℕ) :
    ∃ C : ℝ, 0≤ C ∧ ∀ r : ℝ, 0< r →
      ∀ {Label : Type*} [Fintype Label] [DecidableEq Label]
        (s : Label→SecondBlockSource) (L : Label→Ideal O) (χ ψ : Label→RayCharacter)
        (rows : Finset (Label×O)) (a b : Label×O→ℂ),
      (∀k∈rows,(s k.1).ratio=r) → ∀ E : ℝ, 0≤ E →
      (∀t : ℝ,
        Real.sqrt (∑k∈rows,‖leftColumn Finset.univ
          (actualJointLeft (fun l=>(s l).sector (L l) (χ l) (ψ l)) a k)
          logAnnulus ((s k.1).sector (L k.1) (χ k.1) (ψ k.1)).leftLog t‖^2)*
        Real.sqrt (∑k∈rows,‖rightColumn Finset.univ
          (actualJointRight (fun l=>(s l).sector (L l) (χ l) (ψ l)) b k)
          logAnnulus ((s k.1).sector (L k.1) (χ k.1) (ψ k.1)).rightLog t‖^2)≤
        E*(1+‖t‖)^J) →
      (1+r)^A*‖∑k∈rows,a k*star (b k)*
        secondSectorTerm (s k.1) W (L k.1) (χ k.1) (ψ k.1) k.2‖≤ C*E := by
  obtain ⟨C,hC,hbound⟩ := actual_joint_sector_kernel_bound W (fun _=>logAnnulus)
    (fun _=>Real.log 4) (fun _=>Real.log_nonneg (by norm_num))
    (fun _ _ hn=>CenteredMomentSecondIdealBlockBound.logAnnulus_enclosure _ hn) A J
  refine ⟨C,hC,?_⟩
  intro r hr Label _ _ s L χ ψ rows a b hratio E hE he
  have hh := hbound r hr (fun l=>(s l).sector (L l) (χ l) (ψ l)) rows a b
    (fun k=>(s k.1).rowWeight k.2) (fun k=>(s k.1).rho) (fun k=>(s k.1).x k.2)
    (fun k _=>actual_second_row_weight_norm _ _) (fun _ _=>logAnnulus_norm _)
    (fun _ _=>logAnnulus_norm _) E hE he
  convert hh using 2
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [secondSectorTerm,hratio k hk,actualJointLeft,actualJointRight,
    star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_block_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_physical_block_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_row_weight_norm
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_joint_second_block_bound

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondBlock -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondActive; sha256 51f39d88a6e694626c3cada01dfc11fbbcca2757bdfe3c20c607cc6e2ad80fc2 -/
section
                                               

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSectorLocalization
open CenteredMomentSecondCanonicalScalar CenteredMomentSecondCanonicalFrequency
open CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonical
open CenteredMomentSecondPhysicalBlock CenteredMomentSupport
open Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O

def secondActiveRows {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) : Finset (Label×O) :=
  rows.filter (fun k=>logAnnulus (s k.1).rho≠0 ∧ logAnnulus ((s k.1).x k.2)≠0 ∧
    Squarefree (L k.1) ∧ (s k.1).rowWeight k.2≠0)

/-- Removing only identically vanishing terms preserves the literal sum. -/
theorem actual_second_active_expression {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (χ ψ : Label→RayCharacter) (rows : Finset (Label×O))
    (w : Label×O→ℂ) (W : 𝓢(ℝ,ℂ)) :
    (∑k∈rows,w k*secondSectorTerm (s k.1) W (L k.1) (χ k.1) (ψ k.1) k.2)=
      ∑k∈secondActiveRows s L rows,
        w k*secondSectorTerm (s k.1) W (L k.1) (χ k.1) (ψ k.1) k.2 := by
  rw [secondActiveRows,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h₀ : logAnnulus (s k.1).rho=0
  · simp [h₀,secondSectorTerm,wholeKernel]
  · by_cases h₁ : logAnnulus ((s k.1).x k.2)=0
    · simp [h₁,secondSectorTerm,wholeKernel]
    · by_cases hL : Squarefree (L k.1)
      · by_cases hq : (s k.1).rowWeight k.2=0
        · simp [hq,secondSectorTerm,CanonicalSectorSource.signedWeight]
        · simp [h₀,h₁,hL,hq]
      · simp [h₀,h₁,hL,secondSectorTerm,CanonicalSectorSource.signedWeight,
          SecondBlockSource.sector,UniqueFactorizationMonoid.moebius_of_not_squarefree hL]

theorem actual_second_active_squarefree {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) : Squarefree (L k.1) :=
  (Finset.mem_filter.mp hk).2.2.2.1

theorem actual_second_active_partition {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) :
    canonicalPartition (s k.1).C (s k.1).D (s k.1).inactive
      (nonunitFrequencyGenerator (s k.1).C (s k.1).D (s k.1).inactive*k.2) := by
  have hq := (Finset.mem_filter.mp hk).2.2.2.2
  by_contra hn
  exact hq (by simp [SecondBlockSource.rowWeight,retainedScalar,canonicalPartitionScalar,hn])

theorem actual_second_active_correlation {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O)) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) :
    idealCorrelation (s k.1).C (s k.1).D (s k.1).hC (s k.1).hD
      ((s k.1).frequency*k.2)≠0 :=
  (mul_ne_zero_iff.mp (show (s k.1).rowWeight k.2≠0 from
    (Finset.mem_filter.mp hk).2.2.2.2)).2

theorem actual_second_active_annulus {Label : Type*} (s : Label→SecondBlockSource)
    (L : Label→Ideal O) (rows : Finset (Label×O))
    (hrows : ∀k∈rows,k.2∈(s k.1).rows) (k : Label×O)
    (hk : k∈secondActiveRows s L rows) :
    dyadicScale ((s k.1).dyad 1)/4≤ normValue k.2 ∧
      normValue k.2≤ dyadicScale ((s k.1).dyad 1) := by
  have hx := logAnnulus_support (Finset.mem_filter.mp hk).2.2.1
  have hz : 0< normValue k.2 := by
    rw [normValue_eq_embedding]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero
      ((s k.1).rows_ne _ (hrows k (Finset.mem_filter.mp hk).1))))
  have hH := dyadicScale_pos ((s k.1).dyad 1)
  have hlo := Real.exp_le_exp.mpr hx.1
  have hhi := Real.exp_le_exp.mpr hx.2
  dsimp [SecondBlockSource.x] at hlo hhi
  rw [Real.exp_log (div_pos hz hH),Real.exp_neg,
    Real.exp_log (by norm_num : (0:ℝ)<4)] at hlo
  rw [Real.exp_log (div_pos hz hH),Real.exp_zero] at hhi
  exact ⟨by have hh := (le_div_iff₀ hH).mp hlo; linarith,
    (div_le_one hH).mp hhi⟩

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_expression
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_partition
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_correlation
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_active_annulus

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondActive -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondBatch; sha256 50f1c5744f2fdf67a864ae3fe306ecbe1139df03797f96eb2a6aa3d6a3740777 -/
section
                                                

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
    ∃C : ℝ,0≤ C ∧ ∀{Label : Type*}[Fintype Label][DecidableEq Label]
      (s : Label→SecondBlockSource) (w : Label→ℂ) (r : ℝ),
      0< r → (∀l,(s l).ratio=r) → ∀E : ℝ,0≤ E →
      (∀t : ℝ,secondActiveEnergyPair s w t≤ E*(1+‖t‖)^J) →
        (1+r)^A*‖∑l,w l*(s l).value W‖≤ C*E := by
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

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondBatch -/

/- BEGIN ORIGINAL Cycle61.Physical.InitialMass.SecondWindows; sha256 4bdb009e478f582055f7f767d2be99ea688505539ada11a1b874f61e868fdae4 -/
section
                                                
                                                             

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OAI.SevenEighths.Cycle61InitialMass
noncomputable section
open scoped Classical BigOperators
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentCommonRadialData CenteredMomentCommonSectorWindow
open CenteredMomentCommonWindowColumn CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceRow CenteredMomentRowNorm
open CenteredMomentChildAssembly CenteredMomentSecondSectorColumns CenteredMomentSecondScaled
open CenteredMomentHeckeColumnWindow CenteredMomentSmooth CenteredMomentCauchy
open CenteredMomentLogDyadic CenteredMomentConjugateWindow
open Cycle61Moment RayFourExpansion
local notation "O" => HeckeFamily.O
local instance secondWindowsDecidableSum {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def originalSecondSector (s : Input ι) (R seed : Ideal O) (η : Character) (t : ℝ)
    (A : O) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (L : Ideal O) (χ ψ : RayCharacter)
    (X Y : ℝ) : CanonicalSectorSource where
  C := C
  D := D
  supportedC := hC
  supportedD := hD
  sameSupport := hCD
  pool := finiteColumns (Fintype.piFinset s.pools)
  coefficient := finiteColumnCoefficient (Fintype.piFinset s.pools)
    (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
  character := η
  height := t
  frequency := A
  projector := L
  leftRay := χ
  rightRay := ψ
  leftScale := X
  rightScale := Y

omit [DecidableEq ι] in
theorem actual_second_left_window (s : Input ι) (R seed : Ideal O) (η τ : Character)
    (t θ X Y : ℝ) (A z : O) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (L : Ideal O) (χ ψ : RayCharacter)
    (V : ℝ→ℂ)
    (hτ : ∀I : Ideal O,Supported I → IsCoprime C I → ∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter χ (primaryGenerator I)) :
    let src := originalSecondSector s R seed η t A C D hC hD hCD L χ ψ X Y
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      leftColumn Finset.univ (fun I=>src.leftCoefficient I*idealRowHom z I) V src.leftLog θ=
        windowColumn s C hC R seed L τ t θ X V z := by
  dsimp only
  rw [←actual_sector_window s η τ χ A C hC R seed L t θ X V z hτ]
  congr 1
  simp only [leftColumn,rowPolynomial,CanonicalSectorSource.leftCoefficient,
    CanonicalSectorSource.leftLog,originalSecondSector,CenteredMomentSecondSectorColumns.sectorElement_span]
  apply Finset.sum_congr rfl
  intro I hI
  ring

omit [DecidableEq ι] in
theorem actual_second_right_window (s : Input ι) (R seed : Ideal O) (η τ : Character)
    (t θ X Y : ℝ) (A z : O) (C D : Ideal O) (hC : Supported C) (hD : Supported D)
    (hCD : primeSupport C=primeSupport D) (L : Ideal O) (χ ψ : RayCharacter)
    (V : ℝ→ℂ)
    (hτ : ∀I : Ideal O,Supported I → IsCoprime D I → ∀v : ℝ,
      heightCoeff τ v I=heightCoeff η v I*idealRowHom A I*rayCharacter ψ⁻¹ (primaryGenerator I)) :
    let src := originalSecondSector s R seed η t A C D hC hD hCD L χ ψ X Y
    (Real.sqrt (volume s.toData):ℂ)⁻¹*
      rightColumn Finset.univ (fun I=>src.rightCoefficient I*idealRowHom (-z) I) V src.rightLog θ=
        star (windowColumn s D hD R seed L τ t (-θ) Y (fun x=>star (V x)) (-z)) := by
  dsimp only
  rw [←actual_sector_window s η τ ψ⁻¹ A D hD R seed L t (-θ) Y (fun x=>star (V x)) (-z) hτ]
  have hs : star ((Real.sqrt (volume s.toData):ℂ)⁻¹)=
      (Real.sqrt (volume s.toData):ℂ)⁻¹ := by simp
  simp only [rightColumn,rowPolynomial,CanonicalSectorSource.rightCoefficient,
    CanonicalSectorSource.rightLog,originalSecondSector,
    CenteredMomentSecondSectorColumns.sectorElement_span,star_mul,star_sum,hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [←star_columnPhase,star_star]
  ring

end
end OAI.SevenEighths.Cycle61InitialMass
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_left_window
#print axioms OAI.SevenEighths.Cycle61InitialMass.actual_second_right_window

end
/- END ORIGINAL Cycle61.Physical.InitialMass.SecondWindows -/
