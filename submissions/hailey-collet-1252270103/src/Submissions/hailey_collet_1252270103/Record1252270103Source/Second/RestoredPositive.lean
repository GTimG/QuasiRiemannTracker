/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Exact seed-one source dictionary with the same row puncture and marked slots. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.Second.RestoredRows
import Submissions.hailey_collet_1252270103.Record1252270103Source.Collision.Projector
import Submissions.hailey_collet_1252270103.Record1252270103Restoration.FiniteRows
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SourceRectangleMask

set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OAI.SevenEighths.Record1252270103Second
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentFiniteProfileExceptional
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSecondHeightFamily
open QRH.Record1252270103Restoration Record1252270103Source
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

/-- All actual marked coefficients, with their original normalizing scales. -/
def restoredSlotCoeff (s : Input ι) (i : ι) (I : Ideal O) : ℂ :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

def restoredPlainBound (s : Input ι) : ℝ := max s.b₁ s.b₂

theorem finite_squarefree_plain (ψ : Ideal O →*₀ ℂ)
    (S₁ S₂ : Finset (Ideal O)) (W₁ W₂ : ℝ→ℂ) (b X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hs₁ : Function.support W₁⊆Set.Iic b) (hs₂ : Function.support W₂⊆Set.Iic b)
    (hc₁ : ∀I,W₁ ((I.absNorm:ℝ)/X₁)≠0→I∈S₁)
    (hc₂ : ∀I,W₂ ((I.absNorm:ℝ)/X₂)≠0→I∈S₂) :
    (∑ I : S₁,∑ J : S₂, ordinaryHoleIndicator I J*
      (QRH.Record1252270103KernelMass.squarefreeIndicator ((I:Ideal O)*J):ℂ)*
      ψ ((I:Ideal O)*J)*W₁ ((I.val.absNorm:ℝ)/X₁)*W₂ ((J.val.absNorm:ℝ)/X₂))=
      squarefreePlainSum ψ W₁ W₂ b X₁ X₂ := by
  let f : Ideal O×Ideal O→ℂ := fun n=>ordinaryHoleIndicator n.1 n.2*
    (QRH.Record1252270103KernelMass.squarefreeIndicator (n.1*n.2):ℂ)*
    ψ (n.1*n.2)*W₁ ((n.1.absNorm:ℝ)/X₁)*W₂ ((n.2.absNorm:ℝ)/X₂)
  have hf (n : Ideal O×Ideal O) (hn : f n≠0) :
      n∈S₁×ˢS₂ ∧ n∈plainPairPool b X₁ X₂ := by
    have hw₁ : W₁ ((n.1.absNorm:ℝ)/X₁)≠0 := by
      intro hz; exact hn (by simp [f,hz])
    have hw₂ : W₂ ((n.2.absNorm:ℝ)/X₂)≠0 := by
      intro hz; exact hn (by simp [f,hz])
    have hn₁ : n.1≠0 := by intro hz; exact hn (by simp only [f,hz,zero_mul,map_zero,mul_zero])
    have hn₂ : n.2≠0 := by intro hz; exact hn (by simp only [f,hz,mul_zero,map_zero,zero_mul])
    exact ⟨Finset.mem_product.mpr ⟨hc₁ _ hw₁,hc₂ _ hw₂⟩,
      Finset.mem_product.mpr ⟨(mem_idealBall _ _).mpr ⟨hn₁,(div_le_iff₀ hX₁).mp (hs₁ hw₁)⟩,
        (mem_idealBall _ _).mpr ⟨hn₂,(div_le_iff₀ hX₂).mp (hs₂ hw₂)⟩⟩⟩
  have he : (∑n∈S₁×ˢS₂,f n)=∑n∈plainPairPool b X₁ X₂,f n := by
    calc
      _ = ∑'n,f n := (tsum_eq_sum (fun n hn=>by by_contra hz; exact hn (hf n hz).1)).symm
      _ = _ := tsum_eq_sum (fun n hn=>by by_contra hz; exact hn (hf n hz).2)
  rw [Finset.sum_product] at he
  rw [←Finset.sum_coe_sort S₁] at he
  simp_rw [←Finset.sum_coe_sort S₂] at he
  refine he.trans ?_
  unfold squarefreePlainSum
  apply Finset.sum_congr rfl
  intro n hn
  simp only [f,ordinaryHoleIndicator]
  split_ifs <;> simp

/-- The full tuple source becomes two positive squarefree rows. No marked
pool disjointness, column-nonzero surrogate, or extra row exclusion is used. -/
theorem pure_seed_one_row (s : Input ι) (R : Ideal O) (τ : Character) (t : ℝ) (z : O) :
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      modifiedSourceRow s (sourceModifier 1 1 1 (fun _=>1)) R 1 τ t z=
    squarefreePositiveSlotRow τ (fixedBadMask*idealGenerator R) 1 z
      s.W₁ s.W₂ (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.X₁ s.X₂-
    squarefreePositiveSlotRow τ (fixedBadMask*idealGenerator R) 1 z
      s.W₁ s.W₂ (restoredPlainBound s) s.slots (restoredSlotCoeff s) s.P t s.Y₁ s.Y₂ := by
  classical
  have hs₁ : Function.support (s.W₁:ℝ→ℂ)⊆Set.Iic (restoredPlainBound s) :=
    fun x hx=>(show x≤s.b₁ from s.support₁ hx).trans (le_max_left _ _)
  have hs₂ : Function.support (s.W₂:ℝ→ℂ)⊆Set.Iic (restoredPlainBound s) :=
    fun x hx=>(show x≤s.b₂ from s.support₂ hx).trans (le_max_right _ _)
  let ψ := rowWeight τ (fixedBadMask*idealGenerator R) 1 z t
  have hx := finite_squarefree_plain ψ s.plain₁ s.plain₂ s.W₁ s.W₂
    (restoredPlainBound s) s.X₁ s.X₂ s.X₁_pos s.X₂_pos hs₁ hs₂
    (fun I h=>s.coverage₁ I (Or.inl (by simpa only [one_mul] using h)))
    (fun I h=>s.coverage₂ I (Or.inl (by simpa only [one_mul] using h)))
  have hy := finite_squarefree_plain ψ s.plain₁ s.plain₂ s.W₁ s.W₂
    (restoredPlainBound s) s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos hs₁ hs₂
    (fun I h=>s.coverage₁ I (Or.inr (by simpa only [one_mul] using h)))
    (fun I h=>s.coverage₂ I (Or.inr (by simpa only [one_mul] using h)))
  have hm (v : Tuple ι) :
    sourceModifier 1 1 1 (fun _=>1) v=
      ordinaryHoleIndicator (v (Sum.inr 0)) (v (Sum.inr 1))*
        (QRH.Record1252270103KernelMass.squarefreeIndicator
          (v (Sum.inr 0)*v (Sum.inr 1)):ℂ) := by
    simp only [sourceModifier,coupledFactor,one_mul,mul_one,squarefreeIndicator_cast]
  have hp : Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
    ext v
    simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]
  have hr : modifiedSourceRow s (sourceModifier 1 1 1 (fun _=>1)) R 1 τ t z=
      (squarefreePlainSum ψ s.W₁ s.W₂ (restoredPlainBound s) s.X₁ s.X₂-
       squarefreePlainSum ψ s.W₁ s.W₂ (restoredPlainBound s) s.Y₁ s.Y₂)*
      ∏i,rowSlot τ (fixedBadMask*idealGenerator R) 1 z (s.slots i) (restoredSlotCoeff s i) t := by
    unfold modifiedSourceRow
    rw [hp,sum_tuplePool,live_slot_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hterm (I : s.plain₁) (J : s.plain₂) :
      sourceModifier 1 1 1 (fun _=>1) (pack (fun i=>v i) I J)*
        profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 1
          (pack (fun i=>v i) I J)*rowWeight τ fixedBadMask 1 z t
            (finiteTupleProduct (pack (fun i=>v i) I J))=
      (ordinaryHoleIndicator I J*(QRH.Record1252270103KernelMass.squarefreeIndicator
          ((I:Ideal O)*J):ℂ)*ψ ((I:Ideal O)*J)*
        (s.W₁ ((I.val.absNorm:ℝ)/s.X₁)*s.W₂ ((J.val.absNorm:ℝ)/s.X₂)-
         s.W₁ ((I.val.absNorm:ℝ)/s.Y₁)*s.W₂ ((J.val.absNorm:ℝ)/s.Y₂)))*
        ((∏i,restoredSlotCoeff s i (v i))*ψ (∏i,(v i:Ideal O))) := by
      rw [hm]
      simp only [profileCoefficient,pack_slot,pack_left,pack_right,pack_product,
        one_dvd,ite_true,mul_one,one_mul]
      rw [show _*_ * _ * rowWeight τ fixedBadMask 1 z t ((∏i,(v i:Ideal O))*I*J)=
          (ordinaryHoleIndicator I J*(QRH.Record1252270103KernelMass.squarefreeIndicator
            ((I:Ideal O)*J):ℂ)*(∏i,restoredSlotCoeff s i (v i))*
            idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ I J)*
          ((if IsCoprime ((∏i,(v i:Ideal O))*I*J) R then (1:ℂ) else 0)*
            rowWeight τ fixedBadMask 1 z t ((∏i,(v i:Ideal O))*I*J)) by
            unfold restoredSlotCoeff; ring]
      rw [rowWeight_ideal_mask τ fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)]
      simp only [idealRectangle,map_mul,ψ]
      ring
    rw [←hx,←hy,sub_mul]
    simp only [Finset.sum_mul]
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [hterm]
    ring
  rw [hr]
  unfold squarefreePositiveSlotRow
  rw [s.same_product]
  ring

/-- A marked multiplier stays inside its finite marked tuple sum. This is the
interface for collision inclusion-exclusion; no norm contraction is asserted. -/
theorem seed_one_row_marked_factor (s : Input ι) (g : Ideal O→ℂ)
    (R : Ideal O) (τ : Character) (t : ℝ) (z : O) :
    modifiedSourceRow s
      (fun v=>g (∏i,v (Sum.inl i))*sourceModifier 1 1 1 (fun _=>1) v) R 1 τ t z=
    (squarefreePlainSum (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t)
        s.W₁ s.W₂ (restoredPlainBound s) s.X₁ s.X₂-
     squarefreePlainSum (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t)
        s.W₁ s.W₂ (restoredPlainBound s) s.Y₁ s.Y₂)*
      ∑v : (∀i,s.slots i),g (∏i,(v i:Ideal O))*(∏i,restoredSlotCoeff s i (v i))*
        rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,(v i:Ideal O)) := by
  classical
  have hs₁ : Function.support (s.W₁:ℝ→ℂ)⊆Set.Iic (restoredPlainBound s) :=
    fun x hx=>(show x≤s.b₁ from s.support₁ hx).trans (le_max_left _ _)
  have hs₂ : Function.support (s.W₂:ℝ→ℂ)⊆Set.Iic (restoredPlainBound s) :=
    fun x hx=>(show x≤s.b₂ from s.support₂ hx).trans (le_max_right _ _)
  let ψ := rowWeight τ (fixedBadMask*idealGenerator R) 1 z t
  have hx := finite_squarefree_plain ψ s.plain₁ s.plain₂ s.W₁ s.W₂
    (restoredPlainBound s) s.X₁ s.X₂ s.X₁_pos s.X₂_pos hs₁ hs₂
    (fun I h=>s.coverage₁ I (Or.inl (by simpa only [one_mul] using h)))
    (fun I h=>s.coverage₂ I (Or.inl (by simpa only [one_mul] using h)))
  have hy := finite_squarefree_plain ψ s.plain₁ s.plain₂ s.W₁ s.W₂
    (restoredPlainBound s) s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos hs₁ hs₂
    (fun I h=>s.coverage₁ I (Or.inr (by simpa only [one_mul] using h)))
    (fun I h=>s.coverage₂ I (Or.inr (by simpa only [one_mul] using h)))
  have hp : Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
    ext v
    simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]
  unfold modifiedSourceRow
  rw [hp,sum_tuplePool,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have hterm (I : s.plain₁) (J : s.plain₂) :
    (g (∏i,pack (fun i=>v i) I J (Sum.inl i))*
      sourceModifier 1 1 1 (fun _=>1) (pack (fun i=>v i) I J))*
      profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 1
        (pack (fun i=>v i) I J)*rowWeight τ fixedBadMask 1 z t
          (finiteTupleProduct (pack (fun i=>v i) I J))=
    (ordinaryHoleIndicator I J*(QRH.Record1252270103KernelMass.squarefreeIndicator
        ((I:Ideal O)*J):ℂ)*ψ ((I:Ideal O)*J)*
      (s.W₁ ((I.val.absNorm:ℝ)/s.X₁)*s.W₂ ((J.val.absNorm:ℝ)/s.X₂)-
       s.W₁ ((I.val.absNorm:ℝ)/s.Y₁)*s.W₂ ((J.val.absNorm:ℝ)/s.Y₂)))*
      (g (∏i,(v i:Ideal O))*(∏i,restoredSlotCoeff s i (v i))*ψ (∏i,(v i:Ideal O))) := by
    simp only [sourceModifier,coupledFactor,profileCoefficient,pack_slot,pack_left,
      pack_right,pack_product,one_dvd,ite_true,mul_one,one_mul,←squarefreeIndicator_cast]
    rw [show _*_ * rowWeight τ fixedBadMask 1 z t ((∏i,(v i:Ideal O))*I*J)=
        (g (∏i,(v i:Ideal O))*ordinaryHoleIndicator I J*
          (QRH.Record1252270103KernelMass.squarefreeIndicator ((I:Ideal O)*J):ℂ)*
          (∏i,restoredSlotCoeff s i (v i))*idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ I J)*
        ((if IsCoprime ((∏i,(v i:Ideal O))*I*J) R then (1:ℂ) else 0)*
          rowWeight τ fixedBadMask 1 z t ((∏i,(v i:Ideal O))*I*J)) by
          unfold restoredSlotCoeff; ring]
    rw [rowWeight_ideal_mask τ fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)]
    simp only [idealRectangle,map_mul,ψ]
    ring
  change (∑I : s.plain₁,∑J : s.plain₂,_)=
    (squarefreePlainSum ψ s.W₁ s.W₂ (restoredPlainBound s) s.X₁ s.X₂-
     squarefreePlainSum ψ s.W₁ s.W₂ (restoredPlainBound s) s.Y₁ s.Y₂)*_
  rw [←hx,←hy,sub_mul]
  simp only [Finset.sum_mul]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [hterm]
  ring

/-- Frozen ordinary small-prime exclusions are exactly multiplicative. -/
theorem ordinary_hole_frozen_product (A₁ A₂ I J : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hI : I≠0) (hJ : J≠0) :
    ordinaryHoleIndicator (A₁*I) (A₂*J)=ordinaryHoleIndicator A₁ A₂*ordinaryHoleIndicator I J := by
  have hh : ordinarySmallHole (A₁*I) (A₂*J) ↔ ordinarySmallHole A₁ A₂ ∧ ordinarySmallHole I J := by
    unfold ordinarySmallHole
    simp only [QRH.Record1252270103KernelMass.valuation_mul hA₁ hI,QRH.Record1252270103KernelMass.valuation_mul hA₂ hJ,Nat.add_eq_zero_iff]
    constructor
    · intro h
      exact ⟨fun P hp=>⟨(h P hp).1.1,(h P hp).2.1⟩,
        fun P hp=>⟨(h P hp).1.2,(h P hp).2.2⟩⟩
    · rintro ⟨hA,hIJ⟩ P hp
      exact ⟨⟨(hA P hp).1,(hIJ P hp).1⟩,⟨(hA P hp).2,(hIJ P hp).2⟩⟩
  simp only [ordinaryHoleIndicator,hh]
  split_ifs <;> simp_all

/-- The literal common puncture makes the frozen ordinary squarefree mask
redundant on the remaining ordinary ideals, leaving a constant of norm≤1. -/
theorem frozen_modifier_profile (s : Input ι) (A₁ A₂ D R seed : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R)
    (v : Tuple ι) (hv : v∈Fintype.piFinset s.pools) :
    sourceModifier A₁ A₂ D (fun _=>1) v*
        profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v=
      (QRH.Record1252270103TwoIdeal.squarefreeIndicator (A₁*A₂)*ordinaryHoleIndicator A₁ A₂)*
        sourceModifier 1 1 1 (fun _=>1) v*
          profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v := by
  let prof := profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
  by_cases hz : prof=0
  · change _*prof=_*_*prof
    simp only [hz,mul_zero]
  have hc : IsCoprime (finiteTupleProduct v) R := by
    by_contra hn
    exact hz (by simp [prof,profileCoefficient,hn])
  have hcop : IsCoprime (A₁*A₂) (v (Sum.inr 0)*v (Sum.inr 1)) :=
    ((hc.of_isCoprime_of_dvd_left (plain_product_dvd_tuple v)).of_isCoprime_of_dvd_right hAR).symm
  have hsf : QRH.Record1252270103TwoIdeal.squarefreeIndicator
      ((A₁*v (Sum.inr 0))*(A₂*v (Sum.inr 1)))=
      QRH.Record1252270103TwoIdeal.squarefreeIndicator (A₁*A₂)*
        QRH.Record1252270103TwoIdeal.squarefreeIndicator (v (Sum.inr 0)*v (Sum.inr 1)) := by
    rw [show (A₁*v (Sum.inr 0))*(A₂*v (Sum.inr 1))=(A₁*A₂)*(v (Sum.inr 0)*v (Sum.inr 1)) by ring,
      QRH.Record1252270103TwoIdeal.squarefreeIndicator_mul]
    simp only [QRH.Record1252270103TwoIdeal.coprimalityIndicator,hcop.isRelPrime,ite_true,mul_one]
  have hsf' : QRH.Record1252270103TwoIdeal.squarefreeIndicator
      (A₁*v (Sum.inr 0)*A₂*v (Sum.inr 1))=
      QRH.Record1252270103TwoIdeal.squarefreeIndicator (A₁*A₂)*
        QRH.Record1252270103TwoIdeal.squarefreeIndicator (v (Sum.inr 0)*v (Sum.inr 1)) := by
    simpa only [mul_assoc] using hsf
  have hi := s.pools_ne (Sum.inr 0) _ (Fintype.mem_piFinset.mp hv (Sum.inr 0))
  have hj := s.pools_ne (Sum.inr 1) _ (Fintype.mem_piFinset.mp hv (Sum.inr 1))
  simp only [sourceModifier,coupledFactor,one_mul,mul_one,
    ordinary_hole_frozen_product A₁ A₂ _ _ hA₁ hA₂ hi hj,hsf']
  ring

theorem frozen_source_row_marked_factor (s : Input ι) (g : Ideal O→ℂ)
    (A₁ A₂ D R : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R)
    (τ : Character) (t : ℝ) (z : O) :
    modifiedSourceRow s (fun v=>g (∏i,v (Sum.inl i))*sourceModifier A₁ A₂ D (fun _=>1) v) R 1 τ t z=
      (QRH.Record1252270103TwoIdeal.squarefreeIndicator (A₁*A₂)*ordinaryHoleIndicator A₁ A₂)*
        modifiedSourceRow s (fun v=>g (∏i,v (Sum.inl i))*sourceModifier 1 1 1 (fun _=>1) v) R 1 τ t z := by
  unfold modifiedSourceRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  have h := frozen_modifier_profile s A₁ A₂ D R 1 hA₁ hA₂ hAR v hv
  linear_combination g (∏i,v (Sum.inl i))*rowWeight τ fixedBadMask 1 z t (finiteTupleProduct v)*h

/-- K divides the actual common puncture, so its squarefree interaction with
live marks is exactly a frozen scalar. Its live marked projector is retained. -/
theorem marked_frozen_profile (s : Input ι) (A₁ A₂ D K R seed : Ideal O)
    (F : Ideal O→ℂ) (hKR : K∣R) (v : Tuple ι) :
    Collision.markedSourceModifier A₁ A₂ D K F v*
        profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v=
      QRH.Record1252270103TwoIdeal.squarefreeIndicator K*
        Collision.markedSourceModifier A₁ A₂ D 1 F v*
          profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v := by
  let prof := profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed v
  by_cases hz : prof=0
  · change _*prof=_*_*prof
    simp only [hz,mul_zero]
  have hc : IsCoprime (finiteTupleProduct v) R := by
    by_contra hn
    exact hz (by simp [prof,profileCoefficient,hn])
  have hd : Collision.markedProduct v∣finiteTupleProduct v := by
    unfold Collision.markedProduct finiteTupleProduct
    rw [Fintype.prod_sum_type]
    exact dvd_mul_right _ _
  have hcop : IsCoprime K (Collision.markedProduct v) :=
    ((hc.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hKR).symm
  unfold Collision.markedSourceModifier
  rw [QRH.Record1252270103TwoIdeal.squarefreeIndicator_mul]
  simp only [QRH.Record1252270103TwoIdeal.coprimalityIndicator,hcop.isRelPrime,ite_true,mul_one,one_mul]
  ring

theorem marked_puncture_invariant (K R C : Ideal O) (B : Tuple ι)
    (hKR : K∣R) (hB : finiteTupleProduct B=C) : K*Collision.markedProduct B∣R*C := by
  apply mul_dvd_mul hKR
  rw [←hB]
  unfold Collision.markedProduct finiteTupleProduct
  rw [Fintype.prod_sum_type]
  exact dvd_mul_right _ _

/-- Literal marked-squarefree source, including both frozen ordinary factors
and frozen marked factors. The live marked squarefree sum is still present. -/
theorem marked_seed_one_row (s : Input ι) (A₁ A₂ D K R : Ideal O)
    (hA₁ : A₁≠0) (hA₂ : A₂≠0) (hAR : A₁*A₂∣R) (hKR : K∣R)
    (τ : Character) (t : ℝ) (z : O) :
    modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (fun _=>1)) R 1 τ t z=
      (QRH.Record1252270103TwoIdeal.squarefreeIndicator K*
        QRH.Record1252270103TwoIdeal.squarefreeIndicator (A₁*A₂)*ordinaryHoleIndicator A₁ A₂)*
      ((squarefreePlainSum (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t)
          s.W₁ s.W₂ (restoredPlainBound s) s.X₁ s.X₂-
       squarefreePlainSum (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t)
          s.W₁ s.W₂ (restoredPlainBound s) s.Y₁ s.Y₂)*
        ∑v : (∀i,s.slots i),QRH.Record1252270103TwoIdeal.squarefreeIndicator (∏i,(v i:Ideal O))*
          (∏i,restoredSlotCoeff s i (v i))*
          rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,(v i:Ideal O))) := by
  have hk : modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D K (fun _=>1)) R 1 τ t z=
      QRH.Record1252270103TwoIdeal.squarefreeIndicator K*
        modifiedSourceRow s (Collision.markedSourceModifier A₁ A₂ D 1 (fun _=>1)) R 1 τ t z := by
    unfold modifiedSourceRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    rw [marked_frozen_profile s A₁ A₂ D K R 1 (fun _=>1) hKR v]
    ring
  rw [hk]
  have he : Collision.markedSourceModifier (ι:=ι) A₁ A₂ D 1 (fun _=>1)=
      fun v=>QRH.Record1252270103TwoIdeal.squarefreeIndicator (∏i,v (Sum.inl i))*
        sourceModifier A₁ A₂ D (fun _=>1) v := by
    funext v
    simp only [Collision.markedSourceModifier,one_mul,Collision.markedProduct]
  rw [he,frozen_source_row_marked_factor s _ A₁ A₂ D R hA₁ hA₂ hAR τ t z,
    seed_one_row_marked_factor]
  ring

end
end OAI.SevenEighths.Record1252270103Second
#print axioms OAI.SevenEighths.Record1252270103Second.pure_seed_one_row

#print axioms OAI.SevenEighths.Record1252270103Second.seed_one_row_marked_factor

#print axioms OAI.SevenEighths.Record1252270103Second.frozen_source_row_marked_factor
#print axioms OAI.SevenEighths.Record1252270103Second.marked_frozen_profile

#print axioms OAI.SevenEighths.Record1252270103Second.marked_seed_one_row
