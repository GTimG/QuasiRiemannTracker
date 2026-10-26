/- Copyright (c) 2026 Sil. Apache-2.0.
Actual SMALL contribution through BOTH original finite Cauchy counts.
The four analytic suppliers, native modulus cancellation and all first
reference payments are supplied internally.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSmallSupplierCost
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedFirstFrame

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedSmallFirstCost
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceLiveColumn CenteredMomentAllocationCost
open CenteredMomentFirstSectors CenteredMomentActiveSource
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedSupplierFourthRow MixedSupplierSource
open RepairedRawContext RepairedFirstPoint RepairedFirstFrame RepairedRootParameters RepairedRootCaps RepairedCapEvent
open RepairedRawSupplier RepairedSupplierSplit RepairedFirstScalarBudget
open RepairedSmallMass RepairedSmallCommonProfile RepairedSmallFirstBudget RepairedSmallSupplierCost
open MixedSourceAssembly
open CenteredMomentSecondRetainedAggregate
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M≤H}

theorem uniform_small_first_cost
    (Index : Type v) [Fintype Index] (RootSlot : Index→Type u) [∀k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀k,Fintype.card (RootSlot k)≤N) (ε : ℝ) (hε : 0<ε)
    (Wslot : ℝ→ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot⊆Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1≤Kslot) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)
    (η η₀ : Character) (hQη₀ : Q≤η₀.modulus) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧ ∃C : ℝ,0<C ∧
    ∀ᶠZ : ℝ in atTop,∀k : Index,
    ∀d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀f : Frame d,∀u : Id,Squarefree u → (u.absNorm:ℝ)≤Z^(8:ℝ) →∀tp : ℝ,∀rows : Finset O,
      d.contribution hε false f.label.val.1 u f.tau tp f.scale rows≤
      (C*commonProfile d.root degree control d.t₀ d.V tp)*f.reference*Z^(ε/4)/(u.absNorm:ℝ) := by
  have hδ:=(internal_losses_paid N ε hε).1
  obtain ⟨degree,control,h00,Cp,hCp,hactual⟩:=uniform_small_supplier_cost M H hH
    Index RootSlot N Holes hcard ε hε Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  obtain ⟨Cs,hCs,hsupplier⟩:=uniform_branch_of_raw_cost N (cutoffLoss N ε) hδ
  obtain ⟨Ca,hCa,halloc⟩:=genuine_count_squared (N+2) (cutoffLoss N ε) hδ
  let C:=Cs*Ca*Kslot^(2*N)*Cp*geometryConstant N Kslot
  have hGeom:=constant_pos N Kslot hKslot
  have hC:0<C:=by dsimp only [C]; positivity
  refine ⟨degree,control,h00,C,hC,?_⟩
  filter_upwards [hactual,eventually_event.{u} N ε hε] with Z hactual hevent
  intro k d f u hu hucap tp rows
  -- hterm uses d.choose before the nonzero branch constructs its Point.
  -- Match only these actual first-live indices, never arbitrary Subtypes.
  letI : ∀ B : actualAllocations (tuplePools d.root) f.label.val.1,
      DecidableEq (liveIndices B.val) := fun _=>Classical.decEq _
  have hz:=zero_lt_one.trans d.one_lt_Z
  have hprofile:=common_profile_nonneg d.root degree control d.t₀ d.V tp d.hV
  have hsupp:=(commonLabels_supported _ _ _ f.label.property).1
  have hNC:=(common_norm_caps M H hH d (hcard k) hevent.dimension f.label).1
  have href:0≤f.reference:=by unfold Frame.reference MixedFirstExceptionalNormalization.reference; positivity
  let Mass:=Cs*Kslot^(2*N)*(u.absNorm:ℝ)^(cutoffLoss N ε)/(u.absNorm:ℝ)
  have hMass:0≤Mass:=by dsimp only [Mass]; positivity
  let A:=Cp*commonProfile d.root degree control d.t₀ d.V tp*geometryConstant N Kslot*
    f.reference*Z^(firstLoss N ε)
  have hA:0≤A:=by dsimp only [A]; positivity
  have hterm (B : actualAllocations (tuplePools d.root) f.label.val.1) :
      ‖firstScalar d.root f.label.val.1 B‖^2*
        supplierBranch (allocatedLiveSource d.root (by norm_num) d.cover f.label.val.1 B) (by norm_num)
          u (d.choose hε f.label.val.1 B) (fun L=>¬d.large f.label.val.1 B L) f.tau tp f.scale rows≤A*Mass := by
    by_cases hf:frozenCoefficient B.val f.label.val.1 d.root.R d.root.ν d.root.Wslot d.root.P=0
    · simp only [firstScalar,hf,mul_zero,norm_zero,zero_pow (by decide : 2≠0),zero_mul]
      exact mul_nonneg hA hMass
    · let p:=f.point B hf
      have hn:Fintype.card p.Index≤N:=
        (Fintype.card_le_of_injective (fun i : p.Index=>i.val) Subtype.val_injective).trans (hcard k)
      let Budget:=Cp*commonProfile d.root degree control d.t₀ d.V tp*geometryBudget p
      have hbudget:0≤Budget:=by have hg:=budget_nonneg p; dsimp only [Budget]; positivity
      have hs:=hsupplier hn (1/4) (9/4) p.source (by norm_num) u hu (p.selection hε) Kslot hKslot
        (fun i=>d.hM i.val) (fun L=>¬p.large L) p.tau tp p.scale rows Budget hbudget
        (fun supplier hL=>hactual k d p u hu hucap supplier.1 hL supplier.2 tp rows)
      have hpaid:=paid_geometry p hε (hcard k) hKslot hevent
      have hpaid' : scalar p*Budget≤A := by
        have hh:=mul_le_mul_of_nonneg_left hpaid
          (mul_nonneg (zero_le_one.trans hCp) hprofile)
        have hreference : ref p = f.reference := rfl
        rw [hreference] at hh
        convert hh using 1 <;> simp only [Budget,A] <;> ring
      have hh:=mul_le_mul_of_nonneg_left hs (sq_nonneg ‖firstScalar d.root f.label.val.1 B‖)
      change scalar p*_≤_ at hh
      calc
        _≤scalar p*(Budget*Mass):=hh
        _=(scalar p*Budget)*Mass:=by ring
        _≤A*Mass:=mul_le_mul_of_nonneg_right hpaid' hMass
  have hcountDim:Fintype.card (RootSlot k⊕Fin 2)≤N+2:=by
    simpa only [Fintype.card_sum,Fintype.card_fin] using Nat.add_le_add_right (hcard k) 2
  have hcount:=halloc hcountDim (tuplePools d.root) f.label.val.1 hsupp.1
  have hfinite:d.contribution hε false f.label.val.1 u f.tau tp f.scale rows≤
      (Ca*(f.label.val.1.absNorm:ℝ)^(cutoffLoss N ε))*(A*Mass) := by
    calc
      _≤((actualAllocations (tuplePools d.root) f.label.val.1).card:ℝ)*
          ∑_B : actualAllocations (tuplePools d.root) f.label.val.1,A*Mass := by
        change ((actualAllocations (tuplePools d.root) f.label.val.1).card:ℝ)*_≤_
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum (fun B _=>hterm B)
      _=((actualAllocations (tuplePools d.root) f.label.val.1).card:ℝ)^2*(A*Mass) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
        ring
      _≤_:=mul_le_mul_of_nonneg_right hcount (mul_nonneg hA hMass)
  have hNCδ:(f.label.val.1.absNorm:ℝ)^(cutoffLoss N ε)≤Z^(2*cutoffLoss N ε) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hNC hδ.le).trans_eq
    rw [←Real.rpow_mul hz.le]
  have hNuδ:(u.absNorm:ℝ)^(cutoffLoss N ε)≤Z^(8*cutoffLoss N ε) := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hucap hδ.le).trans_eq
    rw [←Real.rpow_mul hz.le]
  have hpower:Z^(2*cutoffLoss N ε)*Z^(firstLoss N ε)*Z^(8*cutoffLoss N ε)≤Z^(ε/4) := by
    rw [←Real.rpow_add hz,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le
    have he:=total_loss_paid N ε hε
    linarith
  apply hfinite.trans
  calc
    _≤(Ca*Z^(2*cutoffLoss N ε))*
        ((Cp*commonProfile d.root degree control d.t₀ d.V tp*geometryConstant N Kslot*
          f.reference*Z^(firstLoss N ε))*(Cs*Kslot^(2*N)*Z^(8*cutoffLoss N ε)/(u.absNorm:ℝ))) := by
      dsimp only [A,Mass]
      gcongr
    _=(C*commonProfile d.root degree control d.t₀ d.V tp*f.reference/(u.absNorm:ℝ))*
        (Z^(2*cutoffLoss N ε)*Z^(firstLoss N ε)*Z^(8*cutoffLoss N ε)) := by dsimp only [C]; ring
    _≤(C*commonProfile d.root degree control d.t₀ d.V tp*f.reference/(u.absNorm:ℝ))*Z^(ε/4):=
      mul_le_mul_of_nonneg_left hpower (by positivity)
    _=_:=by ring

end
end Candidate.FourthPower.RepairedSmallFirstCost
