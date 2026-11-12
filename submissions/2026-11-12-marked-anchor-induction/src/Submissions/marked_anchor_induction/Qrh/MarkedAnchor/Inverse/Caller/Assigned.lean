/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCaller{Units,Rays,
Integral,Physical,Reference}.lean` (Apache-2.0). Modified by Sil (2026-11-11): the canonical
energy hypothesis `_hmoment` is required only at the quotients of the ASSIGNED sources
`assignedSource S J₁ J₂ lists lists` (the allocations `J₁, J₂` that actually occur: every slot of
`J₁`/`J₂` has a prime in `common ∪ overlap`), instead of at all quotients of `S`. The allocation
sum `all_slots_bound` already uses only these; the other allocation terms vanish identically.
Proofs otherwise unchanged. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerReference

/-!
# Inverse.Caller.Assigned — allocation-restricted caller chain

`actual_physical_reference_bound_assigned` is the plug point of the oracle-parametric clone of the
baseline initialization chain, with the energy oracle needed only for the allocations that occur; this is what makes the subslot widths
`w(slots \ J₁)` controllable (`w(J₁) ≤ B + v + O(η)` on the window).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerBranch
local notation "Eis"=>ActualEisensteinCubic.O
local instance initialEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

theorem assignedSource_mono {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    {S T : Finset (Source (ι:=ι) 0)} (hst : S ⊆ T) (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    assignedSource S J₁ J₂ L₁ L₂ ⊆ assignedSource T J₁ J₂ L₁ L₂ := by
  unfold assignedSource
  apply Finset.image_subset_image
  apply Finset.filter_subset_filter
  exact Finset.product_subset_product_left hst

theorem all_units_bound_assigned (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hbound⟩ := InverseInitialEnergyCallerAllSlots.all_slots_bound N U π hU hπ
  refine ⟨6*C,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hb (u:Eisˣ) :
      ‖∑x∈InverseInitialEnergyCallerUnits.sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
    have hs : InverseInitialEnergyCallerUnits.sourceSector p hp hpr S u⊆S := Finset.filter_subset _ _
    apply hbound p hp hcop hg hinj hpr hc (InverseInitialEnergyCallerUnits.sourceSector p hp hpr S u) u
      (fun x hx=>hdiv x (hs hx)) (fun x hx=>(Finset.mem_filter.mp hx).2)
      pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂ Z D B v θ H R hZ hR
      (fun t ht=>hn t (InverseInitialEnergyCallerUnits.quotientSet_mono p hs ht)) ρ z w
      (fun x hx=>hw x (hs hx)) labels rows hlabels hneg
      (fun x hx=>by
        have hh := hchild x (hs hx)
        rw [(Finset.mem_filter.mp hx).2] at hh
        exact hh) F E hE
    intro J₁ hJ₁ J₂ hJ₂ t ht
    exact hmoment J₁ hJ₁ J₂ hJ₂ t
      (InverseInitialEnergyCallerUnits.quotientSet_mono p (assignedSource_mono hs J₁ J₂ lists lists) ht)
  rw [InverseInitialEnergyCallerUnits.sourceSector_partition p hp hpr S]
  calc
    _≤∑u:Eisˣ,‖∑x∈InverseInitialEnergyCallerUnits.sourceSector p hp hpr S u,w x*rowMode p hp hcop hg hpr pool Ψ j
      slots lists a ω₁ ω₂ Z D B v θ H x ρ z‖ := norm_sum_le _ _
    _≤∑_u:Eisˣ,C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := Finset.sum_le_sum fun u _=>hb u
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,InverseInitialEnergyCallerUnits.unit_sector_card,nsmul_eq_mul];norm_num;ring


theorem all_rays_bound_assigned (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hbound⟩ := all_units_bound_assigned N U π hU hπ
  let A : ℝ := ∑ρ:SecondRayIndex,‖secondRayCoefficient ρ‖
  have hA : 0≤A := Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨C*(1+A),mul_pos hC (by linarith),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hb (ρ:SecondRayIndex) := hbound p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j
    slots hslots lists a ha ω₁ ω₂ Z D B v θ H R hZ hR hn ρ z w hw labels rows
    hlabels hneg hchild F E hE (hmoment ρ)
  rw [Finset.sum_comm]
  calc
    _≤∑ρ:SecondRayIndex,‖∑x∈S,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖ := norm_sum_le _ _
    _≤∑ρ:SecondRayIndex,C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := Finset.sum_le_sum fun ρ _=>hb ρ
    _=C*A*Z^(F+R+π)*E := by simp only [←Finset.sum_mul,←Finset.mul_sum,A]
    _≤C*(1+A)*Z^(F+R+π)*E := by gcongr;linarith


theorem actual_common_integral_bound_assigned (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A:ℝ)(_hA:0≤A)(J:ℕ)
      (g:Fin 6→𝓢(ℝ,ℂ))(g₁ g₂ b₃:𝓢(ℝ,ℂ))(c₁ c₂ θ₁ θ₂ L:ℝ)
      (_hmoment:∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2)),
      ‖∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
        familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z*
        (∑x∈S,∑ρ:SecondRayIndex,w x*rowMode p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
          Z D B v θ H x ρ z)‖≤
        C*Z^(F+R+π)*A*(∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
          tripleHeight J z.1*coordinateHeight J z.2*‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
  obtain ⟨C,hC,hbound⟩ := all_rays_bound_assigned N U π hU hπ
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn w hw labels rows hlabels hneg hchild F A hA J g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L hmoment
  have hb (z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :=
    hbound p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
      Z D B v θ H R hZ hR hn z w hw labels rows hlabels hneg hchild F
      (A*(tripleHeight J z.1*coordinateHeight J z.2))
      (by unfold tripleHeight coordinateHeight;positivity) (hmoment z)
  calc
    _≤∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
      (C*Z^(F+R+π)*A)*(tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L z‖) := by
      apply norm_integral_le_of_norm_le
        ((familyDensity_weighted_integrable g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ L J).const_mul _)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _=_ := integral_const_mul _ _


theorem actual_physical_block_bound_assigned
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (J N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R m η:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A:ℝ)(_hA:0≤A)
      (_hmoment:∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤A*(tripleHeight J z.1*coordinateHeight J z.2)),
      ‖physicalBlock p hp hcop hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(prefactorCenter m D B θ+3*η+F+R+π)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
  obtain ⟨Ce,hCe,he⟩ := actual_common_integral_bound_assigned N U π hU hπ
  obtain ⟨Cp,hCp,hprofile⟩ := initial_physical_family_common_measure
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox 0 J
  refine ⟨Ce*(Cp+1),mul_pos hCe (by linarith),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A hA hmoment
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  obtain ⟨b₃,hb₃⟩ := hprofile Z D B v m θ H η hZp hη
  obtain ⟨hid,hint,hprofileBound⟩ := hb₃ c₁ c₂ θ₁ θ₂ hc₁ hc₂
  let g := secondRootSchwartz V hV hS
  let g₁ := CubicReflectionKernel.logSchwartz W₁ a₀ b₀ ha₀ hs₁ hW₁
  let g₂ := CubicReflectionKernel.logSchwartz W₂ a₀ b₀ ha₀ hs₂ hW₂
  have hb := he p hp hcop hg hinj hpr hc S hdiv pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn w hw labels rows hlabels hneg hchild F A hA J
    g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) hmoment
  have hprof : (∫z:JointLogSeparation.Frequency×(Fin 6→ℝ),
      tripleHeight J z.1*coordinateHeight J z.2*
        ‖familyDensity g g₁ g₂ b₃ c₁ c₂ θ₁ θ₂ (η*Real.log Z) z‖)≤
      (Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) := by
    simp only [pow_zero,one_mul] at hprofileBound
    exact hprofileBound.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  rw [physicalBlock_rectangular_common_measure p hp hcop hg hpr W₁ W₂ Φ V g g₁ g₂ b₃
    Z D B v m θ H η c₁ c₂ θ₁ θ₂ hid pool S hdiv hf w Ψ j slots lists a ω₁ ω₂ hsupport]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZp _)]
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hZp.le _)).trans
  calc
    _≤Z^(prefactorCenter m D B θ+3*η)*
      (Ce*Z^(F+R+π)*A*((Cp+1)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J))) := by gcongr
    _=_ := by
      have hexp : Z^(prefactorCenter m D B θ+3*η+F+R+π)=
          Z^(prefactorCenter m D B θ+3*η)*Z^(F+R+π) := by
        rw [show prefactorCenter m D B θ+3*η+F+R+π=
          (prefactorCenter m D B θ+3*η)+(F+R+π) by ring,Real.rpow_add hZp]
      rw [hexp]
      ring


theorem actual_physical_reference_bound_assigned
    (W₁ W₂:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (Φ:𝓢(ℝ,ℂ))(V:Fin 6→ℝ→ℂ)(M:Fin 6→ℝ)
    (hV:∀i,ContDiff ℝ ∞ (V i))(hS:∀i,HasCompactSupport (V i))
    (hM:∀i,0≤M i)(hbox:∀i y,V i y≠0→|y|≤M i)
    (ω₁ ω₂:ℝ→ℂ)(lo b:ℝ)(hlo:0<lo)(hb:1≤b)
    (hω₁:Function.support ω₁⊆Set.Icc lo b)(hω₂:Function.support ω₂⊆Set.Icc lo b)
    (hd₁:ContDiff ℝ ∞ ω₁)(hd₂:ContDiff ℝ ∞ ω₂) :
    ∃(fresh₁ fresh₂:𝓢(ℝ,ℂ)),
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₁:ℝ→ℂ) ∧
        tsupport (fresh₁:ℝ→ℂ)⊆Set.Icc af bf) ∧
      (∃af bf:ℝ,0<af ∧ af≤bf ∧ HasCompactSupport (fresh₂:ℝ→ℂ) ∧
        tsupport (fresh₂:ℝ→ℂ)⊆Set.Icc af bf) ∧
    ∀(J N:ℕ)(U π:ℝ),0≤U→0<π→∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(_hdiv:∀x∈S,x.divisor⊆x.common)(_hf:∀x∈S,x.frequency≠0)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (Z D B v θ H R m η:ℝ)(_hZ:1<Z)(_hR:R≤U)
      (_hη:0≤η*Real.log Z)(c₁ c₂ θ₁ θ₂:ℝ)(_hc₁:0<c₁)(_hc₂:0<c₂)
      (_hsupport:BlockSupport p (pointSource pool S) W₁ W₂ ω₁ ω₂ V Z D B v θ H c₁ c₂ θ₁ θ₂)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource (unitSector p hp hpr (sourcePoint x ∅ ∅)) x))).2.2∈rows)
      (F A ε:ℝ)(_hA:0≤A)
      (_hδ:max 0 (columnCenter D B v)-columnCenter D B v≤3*η)
      (_hF:F=D-B+θ+(max 0 (columnCenter D B v)-columnCenter D B v))
      (_hReq:R=B-θ+2*η)
      (_hmoment:∀s:ℝ,∀ρ:SecondRayIndex,∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₁ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J) ∧
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest fresh₂ s)
          (Z^(max 0 (columnCenter D B v))) Z F≤(A*Z^(F+ε))*(1+‖s‖)^(2*J)),
      ‖physicalBlock p hp hcop hg (pointSource pool S) (w ∘ erasePoint) Ψ j
        (primeMark slots lists a) (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+11*η+π+ε)*A*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by
  obtain ⟨fresh₁,af₁,bf₁,haf₁,hab₁,hc₁,hsf₁,hu₁⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₁ lo b hlo hb hω₁ hd₁
  obtain ⟨fresh₂,af₂,bf₂,haf₂,hab₂,hc₂,hsf₂,hu₂⟩ :=
    InverseInitialEnergyCallerUniform.initial_raw_uniform ω₂ lo b hlo hb hω₂ hd₂
  refine ⟨fresh₁,fresh₂,⟨af₁,bf₁,haf₁,hab₁,hc₁,hsf₁⟩,⟨af₂,bf₂,haf₂,hab₂,hc₂,hsf₂⟩,?_⟩
  intro J N U π hU hπ
  obtain ⟨C₁,hC₁,hh₁⟩ := hu₁ J
  obtain ⟨C₂,hC₂,hh₂⟩ := hu₂ J
  obtain ⟨Cp,hCp,hphysical⟩ := actual_physical_block_bound_assigned
    W₁ W₂ a₀ b₀ ha₀ hs₁ hs₂ hW₁ hW₂ Φ V M hV hS hM hbox (4*J) N U π hU hπ
  refine ⟨Cp*(C₁+C₂),mul_pos hCp (add_pos hC₁ hC₂),?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    Z D B v θ H R m η hZ hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F A ε hA hδ hF hReq hmoment
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hm : ∀z:JointLogSeparation.Frequency×(Fin 6→ℝ),∀ρ:SecondRayIndex,
      ∀J₁∈slots.powerset,∀J₂∈slots.powerset,∀t∈quotientSet p (assignedSource S J₁ J₂ lists lists),
      normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) ∧
      normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤((C₁+C₂)*(A*Z^(F+ε)))*
          (tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2) := by
    intro z ρ J₁ hJ₁ J₂ hJ₂ t ht
    have hb₁ := hh₁ p hp hcop hg hpr pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
      (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (-leftHeight z)
      hZ (by positivity) (Or.inl rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).1)
    have hb₂ := hh₂ p hp hcop hg hpr pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
      (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
      (by intros;positivity) Z (columnCenter D B v) F (A*Z^(F+ε)) z (rightHeight z)
      hZ (by positivity) (Or.inr rfl) (fun s=>(hmoment s ρ J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [leftHeight_eq] at hb₁
    rw [rightHeight_eq] at hb₂
    have hh : 0≤tripleHeight (4*J) z.1*coordinateHeight (4*J) z.2 := by
      dsimp [tripleHeight,coordinateHeight];positivity
    constructor
    · apply hb₁.trans
      gcongr
      linarith
    · apply hb₂.trans
      gcongr
      linarith
  have hb := hphysical p hp hcop hg hinj hpr hc S hdiv hf pool Ψ hΨ j slots hslots lists a ha
    ω₁ ω₂ Z D B v θ H R m η hZ.le hR hη c₁ c₂ θ₁ θ₂ hc₁ hc₂ hsupport hn
    w hw labels rows hlabels hneg hchild F ((C₁+C₂)*(A*Z^(F+ε))) (by positivity) hm
  apply hb.trans
  have he : prefactorCenter m D B θ+3*η+F+R+π+(F+ε)≤m+11*η+π+ε := by
    rw [hF,hReq]
    exact InverseInitialEnergyCallerClipping.initial_scalar_le m D B v θ η _ π ε hδ
  have hexp := Real.rpow_add hZp (prefactorCenter m D B θ+3*η+F+R+π) (F+ε)
  have hpow := Real.rpow_le_rpow_of_exponent_le hZ.le he
  calc
    _=(Cp*(C₁+C₂))*Z^(prefactorCenter m D B θ+3*η+F+R+π+(F+ε))*A*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)) := by rw [hexp];ring
    _≤_ := by gcongr

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.actual_physical_reference_bound_assigned
