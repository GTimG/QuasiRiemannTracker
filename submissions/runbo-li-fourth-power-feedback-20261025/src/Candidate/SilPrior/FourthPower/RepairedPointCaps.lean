/- Copyright (c) 2026 Sil. Apache-2.0.
All admissibility gates for one ACTUAL first/supplier point. These are
structural/arithmetic consequences, not analytic estimates. Source radii
remain valid when Kchild<1.
-/
import Candidate.SilPrior.FourthPower.RepairedFirstPoint
import Candidate.SilPrior.FourthPower.RepairedSupplierProfiles

set_option autoImplicit false
namespace Candidate.SilPrior.FourthPower.RepairedPointCaps
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ActualEisensteinCubic ConcretePrimeRowBridge
open CenteredMomentFirstSectors CenteredMomentActiveSource CenteredMomentSourceMass
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstActualNonexceptional
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedInnerExceptionalBlock MixedOriginalNormCap MixedOriginalTail MixedFrozenSource
open OuterFreshSource OuterFreshSelected OuterFreshConsumer OuterFreshCutoffAllowance
open RepairedRawSupplier RepairedRawContext RepairedFirstPoint RepairedRootParameters
open RepairedRootCaps RepairedCapEvent RepairedDescendantCaps RepairedChildCaps RepairedConductorCaps
open CenteredMomentSectorLocalization
open OuterFreshWindowPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character} {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀}

local instance (priority := 2000) (p : Point d) : DecidableEq p.Index := Classical.decEq _

structure Bounds (p : Point d) (hε : 0 < ε) (u : Id) (L : Finset p.Index)
    (x : activeFrozen (p.data hε u L)) : Prop where
  card : Fintype.card p.Index ≤ N
  slots : ∀ i,p.source.M i ≤ Kslot
  slotSupport : ∀ i,Function.support (p.source.Wslot i) ⊆ Set.Icc (1:ℝ) 2
  seedSquarefree : Squarefree (residualSeed (p.data hε u L) x)
  seedNorm : ((residualSeed (p.data hε u L) x).absNorm:ℝ) ≤ Z^(8:ℝ)
  radialPos : 0 < p.scale
  radialCap : p.scale ≤ Z^(9:ℝ)
  envelopePos : 0 < secondSourceEnvelope (p.residual hε u L x.val)
  envelopeCap : secondSourceEnvelope (p.residual hε u L x.val) ≤ Z^(2:ℝ)
  sharpCap : sourceNormCap (p.residual hε u L x.val).P (9/4)
    (p.residual hε u L x.val).T (p.residual hε u L x.val).d ≤ Z^(2:ℝ)
  poolCap : MixedOriginalTail.poolCap (p.residual hε u L x.val) ≤ Z^(8:ℝ)
  holeCap : ((p.residual hε u L x.val).Fhole.absNorm:ℝ) ≤ Z^(64:ℝ)
  productCap : (∏ i,2*(p.residual hε u L x.val).P i) ≤ Z^(64:ℝ)
  cutoffPos : 0 < p.cutoff hε u L x.val
  cutoffCap : p.cutoff hε u L x.val ≤ Z^(14:ℝ)
  radiusCap : p.radius hε u L x.val ≤ Z^(15:ℝ)
  familyCap : ∀ y ∈ activeSelected (p.data hε u L),
    OuterFreshAssembly.outerFamilyConductorBudget (p.data hε u L) x.val y
      (p.residual hε u L x.val) p.tau (p.radius hε u L x.val) ≤ Z^(64:ℝ)
  fixedPoolCap : ∀ I ∈ fixedPool (p.data hε u L) x.val (p.residual hε u L x.val)
    (residualSeed (p.data hε u L) x),(I.absNorm:ℝ) ≤ Z^(8:ℝ)
  rawRatioCap : frozenVolume (p.data hε u L)*(selectedVolume (p.data hε u L))^2*
    ((residualSeed (p.data hε u L) x).absNorm:ℝ) ≤ Z^(10:ℝ)

theorem actual_bounds (p : Point d) (hε : 0 < ε) (hcard : Fintype.card ι ≤ N)
    (hevent : Event.{u} N ε Z) (hWs : Function.support Wslot ⊆ Set.Icc (1:ℝ) 2)
    (u : Id) (hu : Squarefree u) (hucap : (u.absNorm:ℝ) ≤ Z^(8:ℝ))
    (L : Finset p.Index) (x : activeFrozen (p.data hε u L)) : Bounds p hε u L x := by
  let q := p.data hε u L
  let r := p.residual hε u L x.val
  have hz := zero_lt_one.trans d.one_lt_Z
  have hfirst := first_product_caps M H hH d hcard hevent p.label.val.1 p.allocation
  have hsupp := residual_support_caps M H hH d hcard hevent p.label.val.1 p.allocation u L
    (p.selection hε L) x.val
  have hcommon := common_norm_caps M H hH d hcard hevent.dimension p.label
  have hx := (Finset.mem_filter.mp x.property).2.2
  have hfrozen := residual_frozen_caps M H hH d hcard hevent p.label.val.1 hcommon.1
    p.allocation u L (p.selection hε L) x.val hx
  have hmod := first_modulus_cap M H hH d hcard hevent.dimension hevent.presentation
    p.label p.inactive p.tau p.modulus
  have hradial : 0 < p.scale := Real.rpow_pos_of_pos hz _
  have hupper := child_upper_cap M H hH d hε hcard hevent p.label p.inactive p.tau p.modulus p.index p.retained
  have hinv := child_inverse_cap M H hH d hε hcard hevent.dimension p.label p.inactive p.index
  have hcuts := second_cutoff_caps r Z p.scale (cutoffLoss N ε) d.one_lt_Z hradial
    (cutoff_le_one N ε hε) hsupp.2.2.2.2.2 hinv
  have hseed := residualSeed_squarefree q hu x
  have hseeddiv : residualSeed q x ∣ u := by
    rw [show u = frozenProduct q x.val*residualSeed q x from residualSeed_spec q x]
    exact dvd_mul_left _ _
  have hseedN : ((residualSeed q x).absNorm:ℝ) ≤ Z^(8:ℝ) :=
    (CenteredExceptionalCount.norm_le_of_dvd hu.ne_zero hseeddiv).trans hucap
  have hWsfirst : ∀ i,Function.support (p.source.Wslot i) ⊆ Set.Icc (1:ℝ) 2 := by
    intro i
    change Function.support (d.root.Wslot i.val) ⊆ _
    rw [d.hcanonical.2.2.2.1]
    exact (slot_profile_support Wslot (33/50) (d.freq i.val)).trans hWs
  have hFhole : (r.Fhole.absNorm:ℝ) ≤ Z^(64:ℝ) := by
    change (d.root.Fhole.absNorm:ℝ) ≤ _
    rw [d.hF,map_one,Nat.cast_one]
    exact Real.one_le_rpow d.one_lt_Z.le (by norm_num)
  have hprod64 := hsupp.2.2.1.trans
    (Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by norm_num : (2:ℝ) ≤ 64))
  have hradius0 : 0 ≤ p.radius hε u L x.val := by
    change 0 ≤ secondSourceCutoff r p.scale * Z^(cutoffLoss N ε / 2)
    exact (mul_pos hcuts.2.1 (Real.rpow_pos_of_pos hz _)).le
  have hfamily (y : Selected q) (hy : y ∈ activeSelected q) :
      OuterFreshAssembly.outerFamilyConductorBudget q x.val y r p.tau (p.radius hε u L x.val) ≤ Z^(64:ℝ) :=
    outer_family_cap hevent q x.val y r p.tau _ hmod hfrozen.2.1 hfrozen.1 (hfrozen.2.2 y hy)
      hsupp.2.2.2.2.1 hradius0 hcuts.2.2.2
  have hfixed (I : Id) (hI : I ∈ fixedPool q x.val r (residualSeed q x)) : (I.absNorm:ℝ) ≤ Z^(8:ℝ) := by
    have hn := (Finset.mem_filter.mp hI).2
    have hcoef : sourceCoefficient r (by norm_num) (residualSeed q x) I ≠ 0 := by
      have he := common_coefficient q x.val r (by norm_num)
        (residual_matches p.source (by norm_num) p.cover u L (p.selection hε L) x.val) (residualSeed q x) I
      rw [he] at hn
      exact right_ne_zero_of_mul hn
    exact ((original_coefficient_cap r (by norm_num) (residualSeed q x) I hcoef).2.trans hsupp.2.2.2.1).trans
      (Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by norm_num))
  have hP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (p.source.hP i)
  have hF : 1 ≤ frozenVolume q := Finset.one_le_prod₀ (fun i _ => p.source.hP i.val)
  have hW : 0 ≤ selectedVolume q := (selectedVolume_pos q hP).le
  have hR : 1 ≤ ∏ i : RestIndex q,p.source.P i.val.val :=
    Finset.one_le_prod₀ (fun i _ => p.source.hP i.val.val)
  have hFW : frozenVolume q*selectedVolume q ≤ Z := by
    apply le_trans _ hfirst.2.1
    change frozenVolume q*selectedVolume q ≤ ∏ i,q.P i
    rw [volume_partition q]
    exact le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hF) hW) hR
  have hWZ : selectedVolume q ≤ Z := (le_mul_of_one_le_left hW hF).trans hFW
  have hratio : frozenVolume q*(selectedVolume q)^2*((residualSeed q x).absNorm:ℝ) ≤ Z^(10:ℝ) := by
    calc
      _ = (frozenVolume q*selectedVolume q)*selectedVolume q*((residualSeed q x).absNorm:ℝ) := by ring
      _ ≤ Z*Z*Z^(8:ℝ) := by gcongr
      _ = _ := by norm_num [Real.rpow_natCast,pow_succ]; ring
  exact ⟨hfirst.1,(fun i => d.hM i.val),hWsfirst,hseed,hseedN,hradial,hupper,hcuts.1,
    hsupp.2.2.2.2.2,hsupp.2.2.2.1,hsupp.2.2.2.2.1,hFhole,hprod64,hcuts.2.1,hcuts.2.2.1,
    hcuts.2.2.2,hfamily,hfixed,hratio⟩

end
end Candidate.SilPrior.FourthPower.RepairedPointCaps
