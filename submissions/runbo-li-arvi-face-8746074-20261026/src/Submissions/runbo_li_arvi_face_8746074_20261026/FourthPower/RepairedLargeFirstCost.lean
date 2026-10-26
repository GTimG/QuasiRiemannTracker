/- Copyright (c) 2026 Sil. Apache-2.0.
Actual LARGE raw contribution through BOTH finite Cauchy counts. All
suppliers are proved internally; first profiles and heights remain in
an explicit rootBudget. No raw-side energy estimate is an input.

-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedPaidFirstBudget
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedFirstFrame
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallMass

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedLargeFirstCost
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentAllocationCost
open CenteredMomentFirstSectors CenteredMomentActiveSource
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource MixedInnerExceptionalBlock
open MixedSupplierFourthRow MixedSupplierSource
open RepairedRawContext RepairedFirstPoint RepairedFirstFrame RepairedRootParameters RepairedRootCaps RepairedCapEvent
open RepairedRawSupplier RepairedSupplierSplit RepairedLargeSupplierBudget RepairedFirstScalarBudget RepairedPaidFirstBudget
open RepairedSmallMass
open MixedSourceAssembly
open CenteredMomentSecondRetainedAggregate
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}

-- Keep the checked Point constructor's concrete classical index instance.
local instance (priority := 2000) {ι : Type u} [Fintype ι]
    {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀}
    (p : Point d) : DecidableEq p.Index := Classical.decEq _

theorem total_loss_paid (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    firstLoss (N:=N) (ε:=ε)+10*cutoffLoss N ε ≤ ε/4 := by
  have hi := (internal_spec N ε hε).2.2.1
  have ho := (omega_spec ε hε).2.2.1
  have hw : windowLoss ε ≤ ε/100 := div_le_div_of_nonneg_right (min_le_right 1 ε) (by norm_num)
  unfold firstLoss cutoffLoss
  linarith

theorem uniform_large_first_cost
    (Index : Type v) [Fintype Index] (RootSlot : Index → Type u) [∀ k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀ k,Fintype.card (RootSlot k) ≤ N) (ε : ℝ) (hε : 0 < ε)
    (Wslot : ℝ → ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot ⊆ Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1 ≤ Kslot) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M)
    (η η₀ : Character) (hQη₀ : Q ≤ η₀.modulus) :
    ∃ U : Controls, ∃ c : Constants, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
    ∀ k : Index, ∀ d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀ f : Frame d, ∀ u : Id, Squarefree u → (u.absNorm:ℝ) ≤ Z^(8:ℝ) →
    ∀ (tp : ℝ) (rows : Finset O),
      d.contribution hε true f.label.val.1 u f.tau tp f.scale rows ≤
      (C*rootBudget d U c tp)*f.reference*Z^(ε/4)/(u.absNorm:ℝ) := by
  have hδ := (internal_losses_paid N ε hε).1
  obtain ⟨U,c,hactual⟩ := uniform_large_supplier_cost (M:=M) (H:=H) (hH:=hH)
    Index RootSlot N Holes hcard ε hε Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  obtain ⟨Cs,hCs,hsupplier⟩ := uniform_branch_of_raw_cost N (cutoffLoss N ε) hδ
  obtain ⟨Ca,hCa,halloc⟩ := genuine_count_squared (N+2) (cutoffLoss N ε) hδ
  let C := Cs*Ca*Kslot^(2*N)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨U,c,C,hC,?_⟩
  filter_upwards [hactual,eventually_event.{u} N ε hε] with Z hactual hevent
  intro k d f u hu hucap tp rows
  have hz := zero_lt_one.trans d.one_lt_Z
  have hroot := rootBudget_nonneg d U c tp hKslot
  have hsupp := (commonLabels_supported _ _ _ f.label.property).1
  have hNC := (common_norm_caps M H hH d (hcard k) hevent.dimension f.label).1
  have href : 0 ≤ f.reference := by
    unfold Frame.reference MixedFirstExceptionalNormalization.reference
    positivity
  let Mass := Cs*Kslot^(2*N)*(u.absNorm:ℝ)^(cutoffLoss N ε)/(u.absNorm:ℝ)
  have hMass : 0 ≤ Mass := by dsimp only [Mass]; positivity
  let A := rootBudget d U c tp*f.reference*Z^(firstLoss (N:=N) (ε:=ε))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hterm (B : actualAllocations (tuplePools d.root) f.label.val.1) :
      ‖firstScalar d.root f.label.val.1 B‖^2*
        supplierBranch (allocatedLiveSource d.root (by norm_num) d.cover f.label.val.1 B) (by norm_num)
          u (d.choose hε f.label.val.1 B) (d.large f.label.val.1 B) f.tau tp f.scale rows ≤ A*Mass := by
    by_cases hf : frozenCoefficient B.val f.label.val.1 d.root.R d.root.ν d.root.Wslot d.root.P = 0
    · simp only [firstScalar,hf,mul_zero,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_mul]
      exact mul_nonneg hA hMass
    · let p := f.point B hf
      have hn : Fintype.card p.Index ≤ N :=
        (Fintype.card_le_of_injective (fun i : p.Index => i.val) Subtype.val_injective).trans (hcard k)
      have hb := coefficients_nonneg p U c tp hKslot
      have hbudget : 0 ≤ budget p U c tp := mul_nonneg (by norm_num)
        (add_nonneg (add_nonneg (add_nonneg hb.1 hb.2.1) hb.2.2.1) hb.2.2.2)
      have hs := hsupplier hn (1/4) (9/4) p.source (by norm_num) u hu (p.selection hε) Kslot hKslot
        (fun i => d.hM i.val) p.large p.tau tp p.scale rows (budget p U c tp) hbudget
        (fun supplier hL => hactual k d p u hu hucap supplier.1 hL supplier.2 tp rows)
      have hpaid := paid_budget d p U c tp hε (hcard k) hKslot hevent
      have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖firstScalar d.root f.label.val.1 B‖)
      change scalar p * _ ≤ _ at hh
      calc
        _ ≤ scalar p*(budget p U c tp*Mass) := hh
        _ = (scalar p*budget p U c tp)*Mass := by ring
        _ ≤ A*Mass := mul_le_mul_of_nonneg_right hpaid hMass
  have hcountDim : Fintype.card (RootSlot k ⊕ Fin 2) ≤ N+2 := by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right (hcard k) 2
  have hcount := halloc hcountDim (tuplePools d.root) f.label.val.1 hsupp.1
  have hfinite : d.contribution hε true f.label.val.1 u f.tau tp f.scale rows ≤
      (Ca*(f.label.val.1.absNorm:ℝ)^(cutoffLoss N ε))*(A*Mass) := by
    calc
      _ ≤ ((actualAllocations (tuplePools d.root) f.label.val.1).card:ℝ)*
          ∑ _B : actualAllocations (tuplePools d.root) f.label.val.1,A*Mass := by
        change ((actualAllocations (tuplePools d.root) f.label.val.1).card:ℝ)*_ ≤ _
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun B _ => hterm B)
      _ = ((actualAllocations (tuplePools d.root) f.label.val.1).card:ℝ)^2*(A*Mass) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount (mul_nonneg hA hMass)
  have hNCδ : (f.label.val.1.absNorm:ℝ)^(cutoffLoss N ε) ≤ Z^(2*cutoffLoss N ε) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hNC hδ.le).trans_eq
    rw [← Real.rpow_mul hz.le]
  have hNuδ : (u.absNorm:ℝ)^(cutoffLoss N ε) ≤ Z^(8*cutoffLoss N ε) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hucap hδ.le).trans_eq
    rw [← Real.rpow_mul hz.le]
  have hpower : Z^(2*cutoffLoss N ε)*Z^(firstLoss (N:=N) (ε:=ε))*Z^(8*cutoffLoss N ε) ≤ Z^(ε/4) := by
    rw [← Real.rpow_add hz,← Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le
    have he := total_loss_paid N ε hε
    linarith
  apply hfinite.trans
  calc
    _ ≤ (Ca*Z^(2*cutoffLoss N ε))*
        ((rootBudget d U c tp*f.reference*Z^(firstLoss (N:=N) (ε:=ε)))*
          (Cs*Kslot^(2*N)*Z^(8*cutoffLoss N ε)/(u.absNorm:ℝ))) := by
      dsimp only [A,Mass]
      gcongr
    _ = (C*rootBudget d U c tp*f.reference/(u.absNorm:ℝ))*
        (Z^(2*cutoffLoss N ε)*Z^(firstLoss (N:=N) (ε:=ε))*Z^(8*cutoffLoss N ε)) := by
      dsimp only [C]
      ring
    _ ≤ (C*rootBudget d U c tp*f.reference/(u.absNorm:ℝ))*Z^(ε/4) :=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _ = _ := by ring

end
end Candidate.FourthPower.RepairedLargeFirstCost
