/- Copyright (c) 2026 Hailey Collet. Released under Apache 2.0.
Exact corrected seed-one dictionary. The rational pool correction retains the
actual marked product M inside every ordinary pair summand. No pool avoidance,
count estimate or coefficient-mask contraction is used in this identity. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Second.RestoredPositive
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.High.CorrectedCenteredData

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OAI.SevenEighths.Record1252270103Source.Collision
noncomputable section
open scoped Classical BigOperators SchwartzMap
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentAddedZeroUniform
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentSourceRectangle
open CenteredMomentHeckeExpansion CenteredMomentHeckeSlots CenteredMomentRectangle
open CenteredMomentSourceRectangleMask CenteredMomentSecondHeightFamily
open QRH.Record1252270103Restoration QRH.Record1252270103Low
open QRH.Record1252270103Source.High.CorrectedCentered
open Record1252270103Second
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι⊕Fin 2) := Classical.decEq _

def correctedPairTerm (P : Finset (Ideal O)) (D M A₁ A₂ : Ideal O)
    (ψ : Ideal O→*₀ℂ) (W₁ W₂ : ℝ→ℂ) (X₁ X₂ Y₁ Y₂ : ℝ)
    (n : QRH.Record1252270103KernelMass.IdealPair) : ℂ :=
  poolCorrection P (D*(M*n.1*n.2))*
    (QRH.Record1252270103KernelMass.squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*
      ψ (n.1*n.2)*frozenProfile W₁ W₂ A₁ A₂ X₁ X₂ Y₁ Y₂ n

theorem corrected_pair_support (s : Input ι) (P : Finset (Ideal O))
    (D M A₁ A₂ : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (ψ : Ideal O→*₀ℂ) (b : ℝ) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b)
    (n : QRH.Record1252270103KernelMass.IdealPair)
    (hn : correctedPairTerm P D M A₁ A₂ ψ s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0) :
    n∈s.plain₁×ˢs.plain₂ ∧ n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂ := by
  have hi : n.1≠0 := by
    intro hz
    exact hn (by simp only [correctedPairTerm,hz,zero_mul,map_zero,mul_zero,zero_mul])
  have hj : n.2≠0 := by
    intro hz
    exact hn (by simp only [correctedPairTerm,hz,mul_zero,map_zero,mul_zero,zero_mul])
  have hhole : ordinarySmallHole (A₁*n.1) (A₂*n.2) := by
    by_contra hh
    exact hn (by simp [correctedPairTerm,frozenProfile,ordinaryHoleIndicator,hh])
  have hsmall : ordinarySmallHole n.1 n.2 := by
    intro p hp
    have hh := hhole p hp
    rw [QRH.Record1252270103KernelMass.valuation_mul hA₁ hi,
      QRH.Record1252270103KernelMass.valuation_mul hA₂ hj] at hh
    exact ⟨(Nat.add_eq_zero_iff.mp hh.1).2,(Nat.add_eq_zero_iff.mp hh.2).2⟩
  have hc : centeredProfile s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n≠0 := by
    intro hz
    exact hn (by simp only [correctedPairTerm,frozenProfile,hz,mul_zero])
  have hor : pairProfile s.W₁ s.W₂ s.X₁ s.X₂ n≠0 ∨
      pairProfile s.W₁ s.W₂ s.Y₁ s.Y₂ n≠0 := by
    by_contra hh
    push Not at hh
    exact hc (by simp only [centeredProfile,hh.1,hh.2,sub_self])
  have hs₁ : Function.support (s.W₁:ℝ→ℂ)⊆Set.Iic b := fun x hx=>(s.support₁ hx).trans hb₁
  have hs₂ : Function.support (s.W₂:ℝ→ℂ)⊆Set.Iic b := fun x hx=>(s.support₂ hx).trans hb₂
  have pack_support (X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
      (hmax₁ : X₁≤max s.X₁ s.Y₁) (hmax₂ : X₂≤max s.X₂ s.Y₂)
      (hw₁ : s.W₁ ((n.1.absNorm:ℝ)/X₁)≠0)
      (hw₂ : s.W₂ ((n.2.absNorm:ℝ)/X₂)≠0) :
      n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂ := by
    have hnorm₁ := (div_le_iff₀ hX₁).mp (hs₁ hw₁)
    have hnorm₂ := (div_le_iff₀ hX₂).mp (hs₂ hw₂)
    have hb : 0≤b := by nlinarith [show (0:ℝ)≤n.1.absNorm from Nat.cast_nonneg _]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hsmall⟩
    · exact (mem_idealBall _ _).mpr ⟨hi,hnorm₁.trans (mul_le_mul_of_nonneg_left hmax₁ hb)⟩
    · exact (mem_idealBall _ _).mpr ⟨hj,hnorm₂.trans (mul_le_mul_of_nonneg_left hmax₂ hb)⟩
  rcases hor with hx|hy
  · have hw := mul_ne_zero_iff.mp hx
    exact ⟨Finset.mem_product.mpr
      ⟨s.coverage₁ _ (Or.inl (by simpa only [one_mul] using hw.1)),
       s.coverage₂ _ (Or.inl (by simpa only [one_mul] using hw.2))⟩,
      pack_support _ _ s.X₁_pos s.X₂_pos (le_max_left _ _) (le_max_left _ _) hw.1 hw.2⟩
  · have hw := mul_ne_zero_iff.mp hy
    exact ⟨Finset.mem_product.mpr
      ⟨s.coverage₁ _ (Or.inr (by simpa only [one_mul] using hw.1)),
       s.coverage₂ _ (Or.inr (by simpa only [one_mul] using hw.2))⟩,
      pack_support _ _ s.Y₁_pos s.Y₂_pos (le_max_right _ _) (le_max_right _ _) hw.1 hw.2⟩

theorem correctedCenteredRow_finite_plain (s : Input ι) (P : Finset (Ideal O))
    (D M A₁ A₂ : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (ψ : Ideal O→*₀ℂ) (b T : ℝ) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b) :
    correctedCenteredRow P D M A₁ A₂ ψ s.W₁ s.W₂ b s.X₁ s.X₂ s.Y₁ s.Y₂ T=
      (Real.sqrt T:ℂ)⁻¹*∑I : s.plain₁,∑J : s.plain₂,
        correctedPairTerm P D M A₁ A₂ ψ s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (I,J) := by
  let f := correctedPairTerm P D M A₁ A₂ ψ s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂
  have hs := corrected_pair_support s P D M A₁ A₂ hA₁ hA₂ ψ b hb₁ hb₂
  have he : (∑n∈commonPool b s.X₁ s.X₂ s.Y₁ s.Y₂,f n)=∑n∈s.plain₁×ˢs.plain₂,f n := by
    calc
      _=∑'n,f n := (tsum_eq_sum (fun n hn=>by by_contra hz;exact hn (hs n hz).2)).symm
      _=_ := tsum_eq_sum (fun n hn=>by by_contra hz;exact hn (hs n hz).1)
  rw [Finset.sum_product,←Finset.sum_coe_sort s.plain₁] at he
  simp_rw [←Finset.sum_coe_sort s.plain₂] at he
  have hf (n) :
      (((P.card:ℝ)/((P.card:ℝ)-(idealDividingPool P (D*(M*n.1*n.2))).card)):ℂ)*
        (QRH.Record1252270103KernelMass.squarefreeIndicator ((A₁*n.1)*(A₂*n.2)):ℂ)*
          ψ (n.1*n.2)*frozenProfile s.W₁ s.W₂ A₁ A₂ s.X₁ s.X₂ s.Y₁ s.Y₂ n=f n := by
    simp only [f,correctedPairTerm,poolCorrection,Complex.ofReal_div,Complex.ofReal_sub,
      Complex.ofReal_natCast]
  unfold correctedCenteredRow
  simp_rw [hf]
  rw [he]

/-- Pointwise identity before either ordinary or marked sum is estimated. -/
theorem corrected_marked_pack (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D K R : Ideal O) (τ : Character) (t : ℝ) (z : O)
    (v : ι→Ideal O) (I J : Ideal O) :
    markedSourceModifier A₁ A₂ D K (poolCorrection P) (pack v I J)*
      profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 1 (pack v I J)*
      rowWeight τ fixedBadMask 1 z t (finiteTupleProduct (pack v I J))=
    (QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*∏i,v i)*
      (∏i,restoredSlotCoeff s i (v i))*
      rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,v i))*
      correctedPairTerm P D (∏i,v i) A₁ A₂
        (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t)
        s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (I,J) := by
  simp only [markedSourceModifier,markedProduct,sourceModifier,coupledFactor,
    profileCoefficient,pack_slot,pack_left,pack_right,pack_product,one_dvd,ite_true,mul_one,one_mul,
    ←squarefreeIndicator_cast]
  have hm := rowWeight_ideal_mask τ fixedBadMask 1 z t (dvd_mul_right _ _) (dvd_mul_left _ _)
    R ((∏i,v i)*I*J)
  change (if IsCoprime ((∏i,v i)*I*J) R then (1:ℂ) else 0)*
    rowWeight τ fixedBadMask 1 z t ((∏i,v i)*I*J)=
      rowWeight τ (fixedBadMask*idealGenerator R) 1 z t ((∏i,v i)*I*J) at hm
  have he : rowWeight τ (fixedBadMask*idealGenerator R) 1 z t ((∏i,v i)*I*J)=
      rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,v i)*
        rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (I*J) := by
    simp only [map_mul,mul_assoc]
  rw [show _*_ * rowWeight τ fixedBadMask 1 z t ((∏i,v i)*I*J)=
      ((QRH.Record1252270103KernelMass.squarefreeIndicator (K*∏i,v i):ℂ)*
        ordinaryHoleIndicator (A₁*I) (A₂*J)*
        (QRH.Record1252270103KernelMass.squarefreeIndicator ((A₁*I)*(A₂*J)):ℂ)*
        poolCorrection P (D*((∏i,v i)*I*J))*(∏i,restoredSlotCoeff s i (v i))*
        idealRectangle s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ I J)*
      ((if IsCoprime ((∏i,v i)*I*J) R then (1:ℂ) else 0)*
        rowWeight τ fixedBadMask 1 z t ((∏i,v i)*I*J)) by
          unfold restoredSlotCoeff
          simp only [mul_assoc]
          ring]
  rw [hm,he]
  simp only [correctedPairTerm,frozenProfile,centeredProfile,pairProfile,idealRectangle,
    restoredSlotCoeff,←squarefreeIndicator_cast]
  ring

/-- The fixed-inducing inlet retains the actual marked product in the exact
rational correction. It uses only the common profile coverage and nonzero
frozen ordinary ideals; there is no amplifier-pool avoidance premise. -/
theorem corrected_marked_seed_one_row (s : Input ι) (P : Finset (Ideal O))
    (A₁ A₂ D K R : Ideal O) (hA₁ : A₁≠0) (hA₂ : A₂≠0)
    (τ : Character) (t : ℝ) (z : O) (b : ℝ) (hb₁ : s.b₁≤b) (hb₂ : s.b₂≤b) :
    (Real.sqrt (s.X₁*s.X₂):ℂ)⁻¹*
      modifiedSourceRow s (markedSourceModifier A₁ A₂ D K (poolCorrection P)) R 1 τ t z=
    ∑v : (∀i,s.slots i),
      (QRH.Record1252270103TwoIdeal.squarefreeIndicator (K*∏i,(v i:Ideal O))*
        (∏i,restoredSlotCoeff s i (v i))*
        rowWeight τ (fixedBadMask*idealGenerator R) 1 z t (∏i,(v i:Ideal O)))*
      correctedCenteredRow P D (∏i,(v i:Ideal O)) A₁ A₂
        (rowWeight τ (fixedBadMask*idealGenerator R) 1 z t)
        s.W₁ s.W₂ b s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) := by
  have hp : Fintype.piFinset s.pools=tuplePool s.slots s.plain₁ s.plain₂ := by
    ext v
    simp only [Fintype.mem_piFinset,tuplePool,tuplePools,Input.pools]
  unfold modifiedSourceRow
  rw [hp,sum_tuplePool,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [correctedCenteredRow_finite_plain s P D (∏i,(v i:Ideal O)) A₁ A₂ hA₁ hA₂
    _ b (s.X₁*s.X₂) hb₁ hb₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  rw [corrected_marked_pack s P A₁ A₂ D K R τ t z]
  ring

end
end OAI.SevenEighths.Record1252270103Source.Collision

#print axioms OAI.SevenEighths.Record1252270103Source.Collision.corrected_pair_support
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.correctedCenteredRow_finite_plain
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.corrected_marked_pack
#print axioms OAI.SevenEighths.Record1252270103Source.Collision.corrected_marked_seed_one_row
