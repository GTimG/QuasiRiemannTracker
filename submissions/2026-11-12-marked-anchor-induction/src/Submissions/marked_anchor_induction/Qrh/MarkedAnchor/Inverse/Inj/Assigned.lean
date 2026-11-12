/- Copyright (c) 2026 Sil. Apache-2.0. -/
/- Adapted from openai_baseline `OAI/NumberTheory/DirichletL/Inversion/InitialEnergyCaller{Sector,
Allocation,Assigned,AssignedPair,AssignedCanonical,Branch,AllSlots}.lean` and
`Descent/{SlotAssignments,SecondAssignedSource}.lean` (Apache-2.0). Modified by Sil (2026-11-12):
the mark is the injective `primeMarkInj`; the assigned sources keep only INJECTIVE slot
assignments (`assignedSourceInj ⊆ assignedSource`), the column energies are
`normalizedColumnEnergyInj`; proofs otherwise unchanged. -/
import Submissions.marked_anchor_induction.Qrh.MarkedAnchor.Inverse.Inj.Column
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerAllSlots

/-!
# Inverse.Inj.Assigned — allocation and assigned sources with injective slot assignments

* `childInj`, `markedModeColumnInj_sector`, `allocatedModeInj`, `rowModeInj_eq_allocations`;
* `primeMarkInj_supported_assignments`: `markInj J L a A = ∑_{q ∈ J.pi (L ∩ A), q injective}
  slotAssignmentWeight J a q`; `paired_primeMarkInj_assignments`;
* `assignedSourceInj S J₁ J₂ L₁ L₂` (injective `q₁`, `q₂`; `⊆ assignedSource`),
  `original_marks_eq_assignedInj`;
* `original_assigned_pair_inj`, `original_assigned_canonical_pair_inj`,
  `actual_allocated_mode_bound_inj`, **`all_slots_bound_inj`** (energy hypotheses at the quotients
  of the injective assigned sources only).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse.Inj
noncomputable section

open scoped BigOperators Classical
open OAI OAI.SevenEighths
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic IdealMobiusDivisorSum
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerCanonical InverseInitialEnergyCallerOpposite InverseInitialProfile
open InverseInitialEnergyCallerAllocation InverseInitialEnergyCallerAssigned
open InverseInitialQuotientGeometry InverseInitialClippedColumns
open Qrh.MarkedAnchor.Inverse
local notation "Eis"=>ActualEisensteinCubic.O

/-! ## Injective slot assignments -/

section Assign
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

/-- An assignment of primes to the slots of `J` is injective. -/
def InjQ (J : Finset σ) (q : ∀ i ∈ J, ι) : Prop :=
  ∀ i (hi : i ∈ J) j (hj : j ∈ J), q i hi = q j hj → i = j

theorem primeMarkInj_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMarkInj I L a A =
      ∑ q ∈ (I.pi (fun i => L i ∩ A)).filter (InjQ I), slotAssignmentWeight I a q := by
  have hF : primeMarkInj I L a A = ∑ p ∈ (I.pi L).filter (InjQ I),
      ∏ i ∈ I.attach, (if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0) := by
    unfold primeMarkInj
    exact Finset.sum_congr (by ext q; simp [InjQ]) (fun _ _ => rfl)
  have hsub : (I.pi (fun i => L i ∩ A)).filter (InjQ I) ⊆ (I.pi L).filter (InjQ I) := by
    intro q hq
    obtain ⟨hq, hinj⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_pi.mpr (fun i hi =>
      (Finset.mem_inter.mp (Finset.mem_pi.mp hq i hi)).1), hinj⟩
  rw [hF, eq_comm]
  calc _ = ∑ p ∈ (I.pi (fun i => L i ∩ A)).filter (InjQ I),
        ∏ i ∈ I.attach, (if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0) := by
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hq' := (Finset.mem_filter.mp hq).1
        unfold slotAssignmentWeight
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [if_pos (Finset.mem_inter.mp (Finset.mem_pi.mp hq' i.1 i.2)).2]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro q hq hnot
      obtain ⟨hq, hinj⟩ := Finset.mem_filter.mp hq
      have : ∃ i, ∃ hi : i ∈ I, q i hi ∉ A := by
        by_contra hall
        push_neg at hall
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_pi.mpr (fun i hi =>
          Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq i hi, hall i hi⟩), hinj⟩)
      obtain ⟨i, hi, hiA⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_attach I ⟨i, hi⟩) (by simp [hiA])

theorem paired_primeMarkInj_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMarkInj J₁ L₁ a₁ A)*primeMarkInj J₂ L₂ a₂ A =
      ∑ q ∈ ((J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A))).filter
          (fun q => InjQ J₁ q.1 ∧ InjQ J₂ q.2),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMarkInj_supported_assignments,primeMarkInj_supported_assignments,
    Finset.filter_product]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

/-- Assigned sources with injective slot assignments on both sides. -/
def assignedSourceInj (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) : Finset (Source (ι:=ι) (J₁.card+J₂.card)) :=
  ((S ×ˢ ((J₁.pi L₁) ×ˢ (J₂.pi L₂))).filter
    (fun z=>(∀ i,pairedSlotAssignment J₁ J₂ z.2 i∈z.1.common∪z.1.overlap) ∧
      (InjQ J₁ z.2.1 ∧ InjQ J₂ z.2.2))).image
      (attachPair J₁ J₂)

theorem assignedSourceInj_subset (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) : assignedSourceInj S J₁ J₂ L₁ L₂ ⊆ assignedSource S J₁ J₂ L₁ L₂ := by
  unfold assignedSourceInj assignedSource
  apply Finset.image_subset_image
  intro z hz
  obtain ⟨hz, hc, _⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz, hc⟩

theorem assignedSourceInj_mono {S T : Finset (Source (ι:=ι) 0)} (hst : S ⊆ T)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    assignedSourceInj S J₁ J₂ L₁ L₂ ⊆ assignedSourceInj T J₁ J₂ L₁ L₂ := by
  unfold assignedSourceInj
  apply Finset.image_subset_image
  apply Finset.filter_subset_filter
  exact Finset.product_subset_product_left hst

theorem assignedSourceInj_sum (S : Finset (Source (ι:=ι) 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ→Finset ι) (F : Source (ι:=ι) (J₁.card+J₂.card)→ℂ) :
    ∑ x∈assignedSourceInj S J₁ J₂ L₁ L₂,F x =
      ∑ y∈S,∑ q∈((J₁.pi (fun i=>L₁ i∩(y.common∪y.overlap))) ×ˢ
        (J₂.pi (fun i=>L₂ i∩(y.common∪y.overlap)))).filter
          (fun q => InjQ J₁ q.1 ∧ InjQ J₂ q.2),F (attachPair J₁ J₂ (y,q)) := by
  rw [assignedSourceInj,Finset.sum_image (fun x _ y _ he=>attachPair_injective J₁ J₂ he),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  have hset : ((J₁.pi L₁ ×ˢ J₂.pi L₂).filter (fun q =>
      (∀ i,pairedSlotAssignment J₁ J₂ q i∈y.common∪y.overlap) ∧ (InjQ J₁ q.1 ∧ InjQ J₂ q.2))) =
      ((J₁.pi (fun i=>L₁ i∩(y.common∪y.overlap))) ×ˢ
        (J₂.pi (fun i=>L₂ i∩(y.common∪y.overlap)))).filter
          (fun q => InjQ J₁ q.1 ∧ InjQ J₂ q.2) := by
    rw [← paired_assignment_filter, Finset.filter_filter]
  exact congrArg (fun s => ∑ q ∈ s, F (attachPair J₁ J₂ (y,q))) hset

theorem original_marks_eq_assignedInj (S : Finset (Source (ι:=ι) 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (w P : Source (ι:=ι) 0→ℂ) :
    (∑ y∈S,w y*(star (primeMarkInj J₁ L₁ a₁ (y.common∪y.overlap))*
      primeMarkInj J₂ L₂ a₂ (y.common∪y.overlap))*P y) =
    ∑ x∈assignedSourceInj S J₁ J₂ L₁ L₂,
      (w (erase x)*coefficient J₁ J₂ a₁ a₂ x)*P (erase x) := by
  rw [assignedSourceInj_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMarkInj_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [coefficient_attach]
  simp only [attachPair,erase_attach]

end Assign

/-! ## Sector, allocation -/

section Alloc
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis)(hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

/-- `InverseInitialEnergyCallerCanonical.child` with the injective mark. -/
def childInj (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (c : InitialChild) : ℂ :=
  finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ (j*primaryGenerator c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a W X

theorem markedModeColumnInj_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumnInj p hp hcop hg hpr pool Ψ j x.frequency x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMarkInj J lists a (x.common∪x.overlap)*
        childInj p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (initialChild (toTuple p (sectorSource u x))) := by
  unfold markedModeColumnInj
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [childInj,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  rfl

theorem markedModeColumnInj_negative_sector
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Z D B v:ℝ) :
    markedModeColumnInj p hp hcop hg hpr pool Ψ j (-x.frequency) x slots lists a W Z D B v=
      ∑J∈slots.powerset,primeMarkInj J lists a (x.common∪x.overlap)*
        childInj p hp hcop hg pool Ψ j (slots\J) lists a W (Z^(columnCenter D B v))
          (negativeChild (initialChild (toTuple p (sectorSource u x)))) := by
  unfold markedModeColumnInj
  rw [hu]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [childInj,negativeChild,initialChild,toTuple,sectorSource,sourceTuple]
  rw [source_quotient p hp x.common x.divisor hdiv]
  simp only [quotient,sourcePoint,mul_neg]

/-- `allocatedMode` with the injective mark. -/
def allocatedModeInj (u:Eisˣ)(pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (x:Source (ι:=ι) 0)(ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) : ℂ :=
  let height := profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2
  modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z *
    (star (primeMarkInj J₁ lists a (x.common∪x.overlap))*
      primeMarkInj J₂ lists a (x.common∪x.overlap))*
    (star (childInj p hp hcop hg pool (secondRayMinus Ψ ρ) j (slots\J₁) lists a
      (childLogTest ω₁ (-height 4)) (Z^(columnCenter D B v))
      (initialChild (toTuple p (sectorSource u x))))*
      childInj p hp hcop hg pool (secondRayPlus Ψ ρ) j (slots\J₂) lists a
      (childLogTest ω₂ (height 5)) (Z^(columnCenter D B v))
      (negativeChild (initialChild (toTuple p (sectorSource u x)))))

theorem rowModeInj_eq_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (x:Source (ι:=ι) 0)(hdiv:x.divisor⊆x.common)(u:Eisˣ)
    (hu:unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ)) :
    rowModeInj p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        allocatedModeInj p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  unfold rowModeInj
  dsimp only
  rw [markedModeColumnInj_sector p hp hcop hg hpr x hdiv u hu,
    markedModeColumnInj_negative_sector p hp hcop hg hpr x hdiv u hu]
  simp only [star_sum,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  simp only [star_mul,allocatedModeInj,modeCoefficient]
  ring

/-! ## Assigned pair and canonical pair -/

include hp in
theorem original_assigned_pair_inj
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (F G:InitialChild→ℂ) :
    ‖∑x∈S,c x*(star (primeMarkInj J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMarkInj J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (F (initialChild (toTuple p (sectorSource u x))))*
        G (initialChild (toTuple p (sectorSource u x))))‖≤
      A*(Real.sqrt (∑t∈quotientSet p (assignedSourceInj S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖F (t,f,k)‖^2)*
        Real.sqrt (∑t∈quotientSet p (assignedSourceInj S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)*
        ∑f∈labels,((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1)*
          ∑k∈rows,‖G (t,f,k)‖^2)) := by
  let T := assignedSourceInj S J₁ J₂ L₁ L₂
  have hs (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :=
    assignedSource_support S J₁ J₂ L₁ L₂ hdiv (assignedSourceInj_subset S J₁ J₂ L₁ L₂ hx)
  have hcoeff (x:Source (ι:=ι) (J₁.card+J₂.card))(hx:x∈T) :
      ‖c (erase x)*coefficient J₁ J₂ a₁ a₂ x‖≤A := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (coefficient_norm_le_one S J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂
        (assignedSourceInj_subset S J₁ J₂ L₁ L₂ hx))
      (norm_nonneg _)).trans (by simpa only [mul_one] using hc (erase x) (hs x hx).1)
  rw [original_marks_eq_assignedInj S J₁ J₂ L₁ L₂ a₁ a₂ c
    (fun x=>star (F (initialChild (toTuple p (sectorSource u x))))*
      G (initialChild (toTuple p (sectorSource u x))))]
  simp only [InverseInitialEnergyCallerAssignedPair.child_erase,←mul_assoc]
  simpa only [←mul_assoc] using InverseInitialEnergyCallerSupport.actual_sector_signed_pair p hp
    hinj hpr T u (fun x hx=>(hs x hx).2.1) (fun x hx=>(hs x hx).2.2) labels rows hlabels
    (fun x hx=>by
      simpa only [InverseInitialEnergyCallerAssignedPair.child_erase] using (hchild (erase x) (hs x hx).1))
    (fun x=>c (erase x)*coefficient J₁ J₂ a₁ a₂ x) A hA hcoeff F G

omit [DecidableEq σ] in
theorem energy_le_moment_inj (pool : Finset ι) (Ψ : Eis →* ℂ) (j : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) (J : ℕ) (T : Finset (Ideal Eis))
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    {Z : ℝ} (hZ : 0<Z) (F B : ℝ)
    (hmoment : ∀ t ∈ T,
      normalizedColumnEnergyInj p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F ≤ B) :
    (∑ t ∈ T, ((idealDivisors t).card:ℝ)^J *
      ∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖childInj p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) ≤
    (Z^F * ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J) * B := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  have heq (t : Ideal Eis) :
      (∑ f ∈ labels, ((idealDivisors f).card:ℝ)^(J+1) *
        ∑ k ∈ rows, ‖childInj p hp hcop hg pool Ψ j slots lists a W X (t,f,k)‖^2) =
      Z^F * normalizedColumnEnergyInj p hp hcop hg pool Ψ (j*primaryGenerator t)
        slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F := by
    unfold normalizedColumnEnergyInj
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow]
    simp only [childInj]
    linear_combination (-(((idealDivisors f).card:ℝ)^(J+1) *
      ‖finiteCanonicalMarkedRowInj p hp hcop hg pool Ψ (j*primaryGenerator t) (primaryGenerator f) k
        slots lists a W X‖^2)) * hr
  calc _ = ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J * (Z^F *
        normalizedColumnEnergyInj p hp hcop hg pool Ψ (j*primaryGenerator t)
          slots lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J+1)) W X Z F) :=
        Finset.sum_congr rfl (fun t _ => by rw [heq t])
    _ ≤ ∑ t ∈ T, ((idealDivisors t).card:ℝ)^J * (Z^F * B) :=
        Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hmoment t ht) (Real.rpow_nonneg hZ.le _)) (by positivity))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem original_assigned_canonical_pair_inj
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)
    (J₁ J₂:Finset σ)(L₁ L₂:σ→Finset ι)(a₁ a₂:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈L₁ i,‖a₁ i q‖≤1)
    (ha₂:∀i∈J₂,∀q∈L₂ i,‖a₂ i q‖≤1)
    (hdiv:∀x∈S,x.divisor⊆x.common)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (c:Source (ι:=ι) 0→ℂ)(A:ℝ)(hA:0≤A)(hc:∀x∈S,‖c x‖≤A)
    (pool:Finset ι)(Ψ₁ Ψ₂:Eis→*ℂ)(j:Eis)(slots₁ slots₂:Finset σ)
    (W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ){Z:ℝ}(hZ:0<Z)(F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSourceInj S J₁ J₂ L₁ L₂),
      normalizedColumnEnergyInj p hp hcop hg pool Ψ₁ (j*primaryGenerator t)
        slots₁ L₁ a₁ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₁ X₁ Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSourceInj S J₁ J₂ L₁ L₂),
      normalizedColumnEnergyInj p hp hcop hg pool Ψ₂ (j*primaryGenerator t)
        slots₂ L₂ a₂ labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        W₂ X₂ Z F≤B₂) :
    ‖∑x∈S,c x*(star (primeMarkInj J₁ L₁ a₁ (x.common∪x.overlap))*
      primeMarkInj J₂ L₂ a₂ (x.common∪x.overlap))*
      (star (childInj p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
          (initialChild (toTuple p (sectorSource u x))))*
        childInj p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
          (negativeChild (initialChild (toTuple p (sectorSource u x)))))‖≤
      A*(Z^F*∑t∈quotientSet p (assignedSourceInj S J₁ J₂ L₁ L₂),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let T := quotientSet p (assignedSourceInj S J₁ J₂ L₁ L₂)
  let f := childInj p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
  let g := childInj p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
  have h₁ := energy_le_moment_inj p hp hcop hg pool Ψ₁ j slots₁ L₁ a₁ W₁ X₁
    (J₁.card+J₂.card) T labels rows hZ F B₁ hmoment₁
  have h₂ := energy_le_moment_inj p hp hcop hg pool Ψ₂ j slots₂ L₂ a₂ W₂ X₂
    (J₁.card+J₂.card) T labels rows hZ F B₂ hmoment₂
  rw [←energy_neg_rows T labels rows hneg (J₁.card+J₂.card) g] at h₂
  have hh := original_assigned_pair_inj p hp hinj hpr
    S u J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ hdiv labels rows hlabels hchild c A hA hc f
    (fun k=>g (negativeChild k))
  apply hh.trans
  calc
    _≤A*(Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₁)*
      Real.sqrt ((Z^F*∑t∈T,((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*B₂)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt h₁)
        (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hA
    _=_ := by
      rw [sqrt_pair_mass _ B₁ B₂ (mul_nonneg (Real.rpow_nonneg hZ.le _)
        (Finset.sum_nonneg fun t ht=>by positivity))]
      ring

theorem actual_allocated_mode_bound_inj
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(hdiv:∀x∈S,x.divisor⊆x.common)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
    (slots J₁ J₂:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (ha₁:∀i∈J₁,∀q∈lists i,‖a i q‖≤1)(ha₂:∀i∈J₂,∀q∈lists i,‖a i q‖≤1)
    (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)(hZ:0<Z)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
    (w:Source (ι:=ι) 0→ℂ)(hw:∀x∈S,‖w x‖≤1)
    (labels:Finset (Ideal Eis))(rows:Finset Eis)
    (hlabels:∀f∈labels,f≠0)(hneg:∀k∈rows,-k∈rows)
    (hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
      (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
    (F B₁ B₂:ℝ)
    (hmoment₁:∀t∈quotientSet p (assignedSourceInj S J₁ J₂ lists lists),
      normalizedColumnEnergyInj p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
        (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
        (Z^(columnCenter D B v)) Z F≤B₁)
    (hmoment₂:∀t∈quotientSet p (assignedSourceInj S J₁ J₂ lists lists),
      normalizedColumnEnergyInj p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
        (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
        (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
        (Z^(columnCenter D B v)) Z F≤B₂) :
    ‖∑x∈S,w x*allocatedModeInj p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
      Z D B v θ H x ρ z‖≤
      ‖secondRayCoefficient ρ‖*(Z^F*∑t∈quotientSet p (assignedSourceInj S J₁ J₂ lists lists),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card))*(Real.sqrt B₁*Real.sqrt B₂) := by
  let c := fun x=>w x*modeCoefficient p hp hcop hg Ψ j Z D B v θ H x ρ z
  have hcoeff (x:Source (ι:=ι) 0)(hx:x∈S) : ‖c x‖≤‖secondRayCoefficient ρ‖ := by
    dsimp only [c]
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw x hx)).trans
      (modeCoefficient_norm_le p hp hcop hg hc Ψ hΨ j Z D B v θ H x ρ z)
  have he := original_assigned_canonical_pair_inj
    p hp hcop hg hinj hpr S u J₁ J₂ lists lists a a ha₁ ha₂ hdiv labels rows hlabels hneg hchild
    c ‖secondRayCoefficient ρ‖ (norm_nonneg _) hcoeff pool (secondRayMinus Ψ ρ) (secondRayPlus Ψ ρ) j
    (slots\J₁) (slots\J₂)
    (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
    (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
    (Z^(columnCenter D B v)) (Z^(columnCenter D B v)) hZ F B₁ B₂ hmoment₁ hmoment₂
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [allocatedModeInj,c]
  ring

theorem rowModeInj_sum_allocations
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (S:Finset (Source (ι:=ι) 0))(hdiv:∀x∈S,x.divisor⊆x.common)(u:Eisˣ)
    (hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
    (pool:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(slots:Finset σ)
    (lists:σ→Finset ι)(a:σ→ι→ℂ)(ω₁ ω₂:ℝ→ℂ)(Z D B v θ H:ℝ)
    (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))(w:Source (ι:=ι) 0→ℂ) :
    (∑x∈S,w x*rowModeInj p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂ Z D B v θ H x ρ z)=
      ∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ∑x∈S,w x*allocatedModeInj p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
  calc
    _=∑x∈S,∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        w x*allocatedModeInj p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [rowModeInj_eq_allocations p hp hcop hg hpr x (hdiv x hx) u (hu x hx)]
      simp only [Finset.mul_sum]
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      exact Finset.sum_comm

end Alloc

/-! ## All slots -/

theorem all_slots_bound_inj (N:ℕ)(U π:ℝ)(hU:0≤U)(hπ:0<π) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ]
      (p:ι→Eis)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (_hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
      (S:Finset (Source (ι:=ι) 0))(u:Eisˣ)(_hdiv:∀x∈S,x.divisor⊆x.common)
      (_hu:∀x∈S,unitSector p hp hpr (sourcePoint x ∅ ∅)=u)
      (pool:Finset ι)(Ψ:Eis→*ℂ)(_hΨ:∀n,‖Ψ n‖≤1)(j:Eis)
      (slots:Finset σ)(_hslots:slots.card≤N)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (_ha:∀i∈slots,∀q∈lists i,‖a i q‖≤1)
      (ω₁ ω₂:ℝ→ℂ)(Z D B v θ H R:ℝ)(_hZ:1≤Z)(_hR:R≤U)
      (_hn:∀t∈quotientSet p S,(t.absNorm:ℝ)≤Z^R)
      (ρ:SecondRayIndex)(z:JointLogSeparation.Frequency×(Fin 6→ℝ))
      (w:Source (ι:=ι) 0→ℂ)(_hw:∀x∈S,‖w x‖≤1)
      (labels:Finset (Ideal Eis))(rows:Finset Eis)
      (_hlabels:∀f∈labels,f≠0)(_hneg:∀k∈rows,-k∈rows)
      (_hchild:∀x∈S,(initialChild (toTuple p (sectorSource u x))).2.1∈labels ∧
        (initialChild (toTuple p (sectorSource u x))).2.2∈rows)
      (F E:ℝ)(_hE:0≤E)
      (_hmoment:∀J₁∈slots.powerset,∀J₂∈slots.powerset,
        ∀t∈quotientSet p (assignedSourceInj S J₁ J₂ lists lists),
        normalizedColumnEnergyInj p hp hcop hg pool (secondRayMinus Ψ ρ) (j*primaryGenerator t)
          (slots\J₁) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₁ (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 4))
          (Z^(columnCenter D B v)) Z F≤E ∧
        normalizedColumnEnergyInj p hp hcop hg pool (secondRayPlus Ψ ρ) (j*primaryGenerator t)
          (slots\J₂) lists a labels rows (fun f=>((idealDivisors f).card:ℝ)^(J₁.card+J₂.card+1))
          (childLogTest ω₂ ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) 5))
          (Z^(columnCenter D B v)) Z F≤E),
      ‖∑x∈S,w x*rowModeInj p hp hcop hg hpr pool Ψ j slots lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E := by
  obtain ⟨C,hC,hmass⟩ := InverseInitialEnergyCallerMass.assigned_quotient_mass (2*N) U π hU hπ
  refine ⟨C*4^N,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hpr hc S u hdiv hu pool Ψ hΨ j slots hslots lists a ha ω₁ ω₂
    Z D B v θ H R hZ hR hn ρ z w hw labels rows hlabels hneg hchild F E hE hmoment
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  let bound := C*‖secondRayCoefficient ρ‖*Z^(F+R+π)*E
  have hb (J₁:Finset σ)(hJ₁:J₁∈slots.powerset)(J₂:Finset σ)(hJ₂:J₂∈slots.powerset) :
      ‖∑x∈S,w x*allocatedModeInj p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
        Z D B v θ H x ρ z‖≤bound := by
    have h₁ := Finset.mem_powerset.mp hJ₁
    have h₂ := Finset.mem_powerset.mp hJ₂
    have he := actual_allocated_mode_bound_inj p hp hcop hg hinj hpr hc S u hdiv pool Ψ hΨ j
      slots J₁ J₂ lists a (fun i hi=>ha i (h₁ hi)) (fun i hi=>ha i (h₂ hi)) ω₁ ω₂
      Z D B v θ H hZp ρ z w hw labels rows hlabels hneg hchild F E E
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).1)
      (fun t ht=>(hmoment J₁ hJ₁ J₂ hJ₂ t ht).2)
    rw [Real.mul_self_sqrt hE] at he
    have hJ : J₁.card+J₂.card≤2*N := by
      have := (Finset.card_le_card h₁).trans hslots
      have := (Finset.card_le_card h₂).trans hslots
      omega
    have hm := hmass p hp S J₁ J₂ lists lists hJ Z R hZ hR hn
    have hm' : (∑t∈quotientSet p (assignedSourceInj S J₁ J₂ lists lists),
        ((idealDivisors t).card:ℝ)^(J₁.card+J₂.card)) ≤ C*Z^(R+π) := by
      refine le_trans ?_ hm
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (InverseInitialEnergyCallerUnits.quotientSet_mono p
          (assignedSourceInj_subset S J₁ J₂ lists lists)) (fun t _ _ => by positivity)
    apply he.trans
    calc
      _≤‖secondRayCoefficient ρ‖*(Z^F*(C*Z^(R+π)))*E := by gcongr
      _=bound := by dsimp only [bound];rw [add_assoc F R π,Real.rpow_add hZp F (R+π)];ring
  rw [rowModeInj_sum_allocations p hp hcop hg hpr S hdiv u hu]
  calc
    _≤∑J₁∈slots.powerset,∑J₂∈slots.powerset,
        ‖∑x∈S,w x*allocatedModeInj p hp hcop hg u pool Ψ j slots J₁ J₂ lists a ω₁ ω₂
          Z D B v θ H x ρ z‖ := (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun J hJ=>norm_sum_le _ _)
    _≤∑_J₁∈slots.powerset,∑_J₂∈slots.powerset,bound :=
      Finset.sum_le_sum fun J₁ hJ₁=>Finset.sum_le_sum fun J₂ hJ₂=>hb J₁ hJ₁ J₂ hJ₂
    _=(4:ℝ)^slots.card*bound := by
      simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)=2*2 by norm_num,mul_pow]
      ring
    _≤(4:ℝ)^N*bound := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hslots) (by dsimp [bound];positivity)
    _=_ := by dsimp [bound];ring

end
end Qrh.MarkedAnchor.Inverse.Inj

#print axioms Qrh.MarkedAnchor.Inverse.Inj.all_slots_bound_inj
