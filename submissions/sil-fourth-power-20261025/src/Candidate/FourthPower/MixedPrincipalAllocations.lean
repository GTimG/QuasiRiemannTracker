/- Copyright (c) 2026 Sil. Apache-2.0.
Genuine allocation pairs for the literal original principal source.
The displayed budget is the actual finite allocation sum. No analytic
pair/source premise is added to the already checked principal supplier.
-/
import Candidate.FourthPower.MixedPrincipalHeights
import Candidate.FourthPower.MixedExceptionalDictionary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.MixedPrincipalAllocations
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile CenteredMomentSourceLiveColumn
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox CenteredMomentSourceMass
open CenteredMomentSourceProfileMass CenteredMomentFirstSectors CenteredMomentLattice
open CenteredMomentAllocatedNaturalRadial CenteredMomentFiniteProfileExceptional
open CenteredMomentHeckeColumnWindow CenteredMomentRowNorm CenteredMomentSecondHeightFamily
open CenteredMomentCommonMaskEnergy
open CenteredMomentSecondSectorColumns
open MixedPrincipalPair MixedPrincipalHeights MixedCommonHeights MixedHeightEnergy
open MixedOriginalSource MixedCommonSource MixedExceptionalDictionary
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedDivisorMask
open MixedLiveNormalization ReferencePrimeEnclosure
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {ι : Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

def tuplePools (s : Source ι a b) := sourcePools s.pool s.d s.hd b s.X₁ s.X₂ s.Y₁ s.Y₂

/-- The enclosure is stated at the original prefixes. The allocated
prefixes only shorten these upper lengths, even below one. -/
def OriginalEnclosure (s : Source ι a b) : Prop :=
  ∀I,Supported I→((I.absNorm:ℝ)≤b*(s.U₁/s.d.1.absNorm)∨
    (I.absNorm:ℝ)≤b*(s.U₂/s.d.2.absNorm))→
      QRH.Record1252270103KernelMass.primeSupport I⊆primeValues s.S

def allocationSource (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G : Id) (B : actualAllocations (tuplePools s) G) : Source ι a b :=
  {s with
    B := B.val
    hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
    G := G
    hprod := (Finset.mem_filter.mp B.property).2
    henclose := by
      let hB := (allocation_data (tuplePools s) G B.val (Finset.mem_filter.mp B.property).1).1
      have hpre (d e : Id) (hd : d≠0) (he : e≠0) (U : ℝ) (hU : 0≤U) :
          U/(d*e).absNorm≤U/d.absNorm := by
        simp only [map_mul,Nat.cast_mul]
        apply div_le_div_of_nonneg_left hU (zero_lt_one.trans_le (ideal_norm_one_le hd))
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (ideal_norm_one_le he)
      intro I hI hlen
      apply cover I hI
      rcases hlen with hlen|hlen
      · exact Or.inl (hlen.trans (mul_le_mul_of_nonneg_left
          (hpre s.d.1 (B.val (Sum.inr 0)) s.hd.1 (hB _) s.U₁
            ((s.hL.trans_le s.hX₁).trans_le s.hXU₁).le) hb))
      · exact Or.inr (hlen.trans (mul_le_mul_of_nonneg_left
          (hpre s.d.2 (B.val (Sum.inr 1)) s.hd.2 (hB _) s.U₂
            ((s.hL.trans_le s.hX₂).trans_le s.hXU₂).le) hb))}

theorem allocation_admissible (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (N : ℕ) (Bcap Z : ℝ) (hι : Fintype.card ι≤N)
    (hF : (s.Fhole.absNorm:ℝ)≤Z^Bcap) (hP : (∏i,2*s.P i)≤Z^Bcap)
    (G : Id) (B : actualAllocations (tuplePools s) G) :
    (allocationSource s hb cover G B).Admissible N Bcap Z := by
  refine ⟨?_,hF,?_⟩
  · change Fintype.card (liveIndices B.val)≤N
    apply le_trans _ hι
    rw [Fintype.card_coe]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  · change (∏i : liveIndices B.val,2*s.P i.val)≤Z^Bcap
    apply le_trans _ hP
    rw [Finset.prod_coe_sort (liveIndices B.val) (fun i=>2*s.P i)]
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ _)
      (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i)))
      (fun i _ _=>by linarith [s.hP i])

/-- The literal original source after an independent residual height. -/
def originalRow (s : Source ι a b) (ha : 0<a) (χ : Character)
    (G : Id) (hG : G≠0) (seed D : Id) (v : ℝ) : ℂ :=
  originalMaskedRow χ s.S s.H s.pool s.d s.hd G s.R seed D hG
    (fun i=>heightCoefficient (s.ν i) v) s.Wslot s.P
    (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) (s.t₁+v))
    (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) (s.t₂+v))
    b s.X₁ s.X₂ s.Y₁ s.Y₂

/-- Exact complete genuine allocation identity, with no coefficient
replacement. The seed is removed only because seed divides G. -/
theorem original_row_allocated (s : Source ι a b) (ha : 0<a) (hb : 0≤b)
    (cover : OriginalEnclosure s) (χ : Character) (G : Id) (hG : G≠0)
    (seed D : Id) (hseed : seed∣G) (v : ℝ) :
    originalRow s ha χ G hG seed D v=
      ∑B : actualAllocations (tuplePools s) G,
        (shiftSource (allocationSource s hb cover G B) v).row ha χ D := by
  unfold originalRow
  rw [original_masked_row_eq χ s.S s.H s.pool s.hp s.d s.hd G s.R seed D hG hseed]
  rfl

/-- Exact normalization of the original sector at any height and either
row position. This is the physical dictionary needed by the window pair. -/
theorem original_sector_norm (s : Source ι a b) (ha : 0<a)
    (η : Character) (G : Id) (hG : Supported G) (seed D : Id) (v : ℝ)
    (z : O) (hz : z≠0) :
    let Qsource := finiteColumns (Fintype.piFinset (tuplePools s))
    let β := originalColumn s.S s.H s.pool s.d s.hd s.R seed s.ν s.Wslot s.P
      (normPowerProfile s.W₁ a b ha s.hs₁ (s.W₁.smooth ⊤) s.t₁)
      (normPowerProfile s.W₂ a b ha s.hs₂ (s.W₂.smooth ⊤) s.t₂)
      b s.X₁ s.X₂ s.Y₁ s.Y₂
    ‖normalization (s.X₁*s.X₂) s.P*
      rowPolynomial Finset.univ (sectorElement G hG.1 Qsource)
        (fun I : sectorPool G hG.1 Qsource=>(if D∣I.val then β (G*I) else 0)*
          heightCoeff η v I) z‖=
      ‖originalRow s ha (naturalCharacter η z) G hG.1 seed D v‖ := by
  dsimp only
  have h := congrArg norm (original_sector_height s.S s.H s.pool s.hp s.d s.hd s.R seed
    s.ν s.Wslot s.P s.W₁ s.W₂ (s.t₁/(2*Real.pi)) (s.t₂/(2*Real.pi))
    b s.X₁ s.X₂ s.Y₁ s.Y₂ (s.hL.trans_le s.hX₁) (s.hL.trans_le s.hX₂)
    (s.hL.trans_le s.hY₁) (s.hL.trans_le s.hY₂) (s.hpX.trans s.hpY.symm) η G hG D v z hz)
  have hphase := residual_phase_norm (s.X₁*s.X₂) (by rw [s.hpX];exact s.total_pos)
    s.d s.hd G hG.1 v
  simpa only [originalRow,tuplePools,norm_power_profile_phase,add_div,norm_mul,hphase,one_mul] using h

def pairBudget (s : Source ι a b) (hb : 0≤b) (cover : OriginalEnclosure s)
    (G₁ G₂ : Id) (J : ℕ) (control : Finset (ℕ×ℕ)) (Z ε α : ℝ) : ℝ :=
  ∑p : actualAllocations (tuplePools s) G₁ × actualAllocations (tuplePools s) G₂,
    (allocationSource s hb cover G₁ p.1).budget J control Z ε*
      (allocationSource s hb cover G₂ p.2).budget J control Z ε*
      min ((allocationSource s hb cover G₁ p.1).saving α)
        ((allocationSource s hb cover G₂ p.2).saving α)

private theorem weighted_sum_exchange {Λ : Type*} [Fintype Λ]
    (Ds : Finset Id) (rows : Finset O) (μ : Id→ℂ) (f : Id→O→Λ→ℝ) :
    (∑D∈Ds,‖μ D‖*∑z∈rows,∑p,f D z p)=
      ∑p,∑D∈Ds,‖μ D‖*∑z∈rows,f D z p := by
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑D∈Ds,∑p,∑z∈rows,‖μ D‖*f D z p := by
      apply Finset.sum_congr rfl
      intro D hD
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

/-- Complete original-coefficient pair, with a visible exact genuine
allocation budget. All analytic pair estimates are discharged internally.
The artificial mask D is summed; neither genuine common norm is dropped. -/
theorem uniform_original_height_pair (N : ℕ) (α Bcap a b ε δ : ℝ)
    (hα : 0≤α) (hα4 : α<4/5) (hBcap : 0≤Bcap)
    (ha : 0<a) (hb : 0≤b) (hε : 0<ε) (hδ : 0<δ) (hgap : α+2*δ<1) :
    ∃J : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧
      ∀Q : Id,Q≠0→∃C : ℝ,0<C ∧
      ∀(ι : Type u) [Fintype ι],∀s : Source ι a b,
      ∀cover : OriginalEnclosure s,∀Z : ℝ,1≤Z→Fintype.card ι≤N→
      (s.Fhole.absNorm:ℝ)≤Z^Bcap→(∏i,2*s.P i)≤Z^Bcap→
      ∀G₁ G₂ : Id,∀hG₁ : G₁≠0,∀hG₂ : G₂≠0,∀seed : Id,seed∣G₁→seed∣G₂→
      ∀(v₁ v₂ : ℝ)(η₁ η₂ : Character)(rows : Finset O)(Ds : Finset Id)(μ : Id→ℂ),
      (∀z∈rows,z≠0)→(∀D∈Ds,Squarefree D)→(∀D∈Ds,‖μ D‖≤1)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound η₁
        (fixedBadMask*idealGenerator ((s.R*G₁)*D)) 1 z:ℝ)≤Z^Bcap)→
      (∀z∈rows,∀D∈Ds,(HeckeRowClosure.rowConductorBound η₂
        (fixedBadMask*idealGenerator ((s.R*G₂)*D)) 1 (-z):ℝ)≤Z^Bcap)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow η₁ Q fixedBadMask 1 z)→
      (∀z∈rows,CenteredExceptionalProfile.FixedInducingRow η₂ Q fixedBadMask 1 (-z))→
      (∑D∈Ds,‖μ D‖*∑z∈rows,
        ‖originalRow s ha (naturalCharacter η₁ z) G₁ hG₁ seed D v₁‖*
        ‖originalRow s ha (naturalCharacter η₂ (-z)) G₂ hG₂ seed D v₂‖)≤
      (rows.card:ℝ)*C*pairBudget s hb cover G₁ G₂ J control Z ε α*
        (1+‖v₁‖)^J*(1+‖v₂‖)^J := by
  obtain ⟨J,control,h00,hpair⟩ := uniform_shifted_pair_rows N α Bcap a b ε δ
    hα hα4 hBcap ha hb hε hδ hgap
  refine ⟨J,control,h00,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hpair⟩ := hpair Q hQ
  refine ⟨C,hC,?_⟩
  intro ι instι s cover Z hZ hι hF hP G₁ G₂ hG₁ hG₂ seed hs₁ hs₂ v₁ v₂
    η₁ η₂ rows Ds μ hrows hDs hμ hc₁ hc₂ he₁ he₂
  let Λ := actualAllocations (tuplePools s) G₁ × actualAllocations (tuplePools s) G₂
  let left := fun B : actualAllocations (tuplePools s) G₁=>allocationSource s hb cover G₁ B
  let right := fun B : actualAllocations (tuplePools s) G₂=>allocationSource s hb cover G₂ B
  let f := fun (D : Id)(z : O)(p : Λ)=>
    ‖(shiftSource (left p.1) v₁).row ha (naturalCharacter η₁ z) D‖*
    ‖(shiftSource (right p.2) v₂).row ha (naturalCharacter η₂ (-z)) D‖
  have htriangle (D : Id) (z : O) :
      ‖originalRow s ha (naturalCharacter η₁ z) G₁ hG₁ seed D v₁‖*
        ‖originalRow s ha (naturalCharacter η₂ (-z)) G₂ hG₂ seed D v₂‖≤∑p : Λ,f D z p := by
    rw [original_row_allocated s ha hb cover _ G₁ hG₁ seed D hs₁ v₁,
      original_row_allocated s ha hb cover _ G₂ hG₂ seed D hs₂ v₂]
    apply (mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _=>norm_nonneg _))).trans_eq
    simp only [Λ,f,left,right,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
  have hp (p : Λ) := hpair ι ι (left p.1) (right p.2) Z hZ
    (allocation_admissible s hb cover N Bcap Z hι hF hP G₁ p.1)
    (allocation_admissible s hb cover N Bcap Z hι hF hP G₂ p.2)
    v₁ v₂ η₁ η₂ rows Ds μ hrows hDs hμ hc₁ hc₂ he₁ he₂
  calc
    _ ≤ ∑D∈Ds,‖μ D‖*∑z∈rows,∑p : Λ,f D z p := by
      apply Finset.sum_le_sum
      intro D hD
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.sum_le_sum (fun z _=>htriangle D z)
    _ = ∑p : Λ,∑D∈Ds,‖μ D‖*∑z∈rows,f D z p := weighted_sum_exchange Ds rows μ f
    _ ≤ ∑p : Λ,(rows.card:ℝ)*(C*((left p.1).budget J control Z ε*
        (right p.2).budget J control Z ε)*min ((left p.1).saving α) ((right p.2).saving α))*
          (1+‖v₁‖)^J*(1+‖v₂‖)^J := by
      apply Finset.sum_le_sum
      intro p hp₀
      exact hp p
    _ = _ := by
      unfold pairBudget
      dsimp only [Λ,left,right]
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp₀
      ring

end
end Candidate.FourthPower.MixedPrincipalAllocations
