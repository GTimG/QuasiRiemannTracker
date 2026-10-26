/- Copyright (c) 2026 Sil. Apache-2.0.
The four proved small providers at the ACTUAL residual source and radius.
All constants precede the root, both allocations, the seed and the height.
Only structural and numeric caps are supplied by the caller. 
-/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedSmallRootFamily
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedSmallAdmission
import Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.RepairedPointCaps

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.RepairedSmallPoint
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentCommonProfile CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceLiveColumn CenteredMomentFirstSectors
open CenteredMomentActiveSource CenteredMomentHeckeColumnWindow CenteredMomentFirstAmplificationChoice
open CenteredMomentSourceRow CenteredMomentSectorLocalization
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedFirstLiveSource
open MixedFirstActualNonexceptional MixedCanonicalSource MixedFirstAvoidance MixedOriginalNormCap
open MixedSupplierFourthRow MixedSupplierSource MixedOriginalTail MixedInnerExceptionalLedger
open OuterFreshSource OuterFreshSelectedWindow OuterFreshCutoffAllowance
open RepairedSmallRootFamily RepairedSmallAdmission RepairedSmallCommonProfile RepairedSmallFourShapes
open RepairedRootParameters RepairedRawContext RepairedFirstPoint RepairedPointCaps
open RepairedRootCaps RepairedCapEvent RepairedDescendantCaps RepairedChildCaps RepairedConductorCaps
open RepairedRawSupplier
open CenteredMomentOriginalChildEnergy
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

-- Exactly the first-live Point index; no instance for nested residual subtypes.
local instance (priority := 2000) {κ : Type u} [Fintype κ]
    {Wslot : ℝ→ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ} {η η₀ : Character}
    {d : RootInput M H hH κ Wslot N Holes ε Z Kslot η η₀}
    (p : Point d) : DecidableEq p.Index := Classical.decEq _


def nativeLoss (N : ℕ) (ε : ℝ) : ℝ := (3/4:ℝ)*widthFloor ε+11*cutoffLoss N ε
def exceptionalLoss (N : ℕ) (ε : ℝ) : ℝ := 19*cutoffLoss N ε
def zeroLoss (N : ℕ) (ε : ℝ) : ℝ := 8*cutoffLoss N ε

theorem numeric_gates (N : ℕ) (ε : ℝ) (hε : 0<ε) :
    mesh ε≤windowCap N ε ∧ (3:ℝ)≤windowCap N ε ∧ cutoffLoss N ε<1/8 := by
  have hm:=mesh_spec ε hε
  have hn:=mul_nonneg (Nat.cast_nonneg N) hm.1.le
  have hi:=(internal_spec N ε hε).2.2.1
  have ho:=(omega_spec ε hε).2.2.2
  refine ⟨?_,?_,?_⟩
  · unfold windowCap
    norm_num [rootReserve] at hm
    linarith
  · unfold windowCap
    linarith
  · unfold cutoffLoss
    linarith

/-- Literal small Gauss conclusion over ABSTRACT Sources. This definition
contains no estimate assumption and preserves the original root profile. -/
def GaussBound {ρ κ : Type u} [Fintype ρ] [Fintype κ]
    (root : Source ρ (1/4) (9/4)) (r : Source κ (1/4) (9/4))
    (N : ℕ) (ε Z : ℝ) (degree : ℕ) (control : Finset (ℕ×ℕ))
    (C t₀ V : ℝ) (σ : Character) (u seed : Id) (tp K : ℝ) : Prop :=
  (sourceGaussEnergy (sourceColumns r) (sourceCoefficient r (by norm_num) seed)
    (heightCoeff σ tp) ballProfile K).re ≤
    C*commonProfile root degree control t₀ V tp*
      fullShape r σ u seed K Z (nativeLoss N ε) (exceptionalLoss N ε) (zeroLoss N ε) 40

section CompactConclusion
variable {M H hH}

/-- Exactly the original all-supplier Point conclusion, now named once.
All u/seed, smallness, sigma-modulus, height and Source data are unchanged. -/
def Result {κ : Type u} [Fintype κ] {Wslot : ℝ→ℂ} {N Holes : ℕ}
    {ε Z Kslot : ℝ} {η η₀ : Character}
    {d : RootInput M H hH κ Wslot N Holes ε Z Kslot η η₀}
    (p : Point d) (hε : 0 < ε) (degree : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : Prop :=
  ∀u : Id,Squarefree u → (u.absNorm:ℝ) ≤ Z^(8:ℝ) →
  ∀L : Finset p.Index,¬p.large L → ∀x : activeFrozen (p.data hε u L),
  ∀σ : Character,
    σ.modulus.absNorm ≤ p.tau.modulus.absNorm*
      (ReferenceCubicCharacter.conductorConstant*(frozenProduct (p.data hε u L) x.val).absNorm)*
        (Ideal.span {(12:O)}).absNorm → ∀tp : ℝ,
  GaussBound d.root (p.residual hε u L x.val) N ε Z degree control C d.t₀ d.V
    σ u (residualSeed (p.data hε u L) x) tp p.scale

end CompactConclusion
theorem uniform_small_point
    (Index : Type v) [Fintype Index] (RootSlot : Index→Type u) [∀k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀k,Fintype.card (RootSlot k)≤N) (ε : ℝ) (hε : 0<ε)
    (Wslot : ℝ→ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot⊆Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1≤Kslot) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M)
    (η η₀ : Character) (hQη₀ : Q≤η₀.modulus) :
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),(0,0)∈control ∧ ∃C : ℝ,1≤C ∧
    ∀ᶠZ : ℝ in atTop,∀k : Index,
    ∀d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀p : Point d,Result p hε degree control C := by
  have hδ:=(internal_losses_paid N ε hε).1
  have hg:=numeric_gates N ε hε
  obtain ⟨degree,control,h00,hbase⟩ := uniform_root_full_gauss M H hH Index RootSlot N Holes hcard Wslot
    (1/4) (9/4) 40 3 (mesh ε) (windowCap N ε) 16 4 0 8 (widthFloor ε)
    (cutoffLoss N ε) (cutoffLoss N ε) (cutoffLoss N ε) (33/50) (33/50) 15 1
    (cutoffLoss N ε) 9 1 64 (cutoffLoss N ε) (cutoffLoss N ε) (cutoffLoss N ε)
    (cutoffLoss N ε) 16 8 (cutoffLoss N ε) 40 Kslot
    hWs hW (by norm_num) (by norm_num) (by norm_num) (mesh_spec ε hε).1.le hg.1
    (by norm_num) (by norm_num) hg.2.1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hδ hδ hδ (by norm_num) (by norm_num) hδ (by norm_num) (by norm_num)
    (by norm_num) hδ hδ hg.2.2 hδ hδ (by norm_num) hδ hKslot hβ Q hQt hQ72 hQM
  obtain ⟨C,hC,hbase⟩:=hbase η₀ hQη₀
  refine ⟨degree,control,h00,C,hC,?_⟩
  filter_upwards [hbase,eventually_event.{u} N ε hε] with Z hbase hevent
  intro k d p
  unfold Result
  intro u hu hucap L hsmall x σ hσ tp
  unfold GaussBound
  let q:=p.data hε u L
  let r:=p.unavoided hε u L x.val
  let seed:=residualSeed q x
  let i : SupplierShape Index RootSlot:=⟨k,liveIndices p.allocation.val,L,p.selection hε L⟩
  have hadmit:=actual_small_residual M H hH d hε p.label.val.1 u p.allocation L hsmall
  have hFacts:=hadmit.2.2.2 x.val
  have hcan : Canonical M H hH Wslot 16 (windowCap N ε) Z η₀
      (fun j : RestIndex q=>d.chars j.val.val.val) (fun j=>d.w j.val.val.val)
      (fun _=>33/50) (fun j=>d.freq j.val.val.val) d.t₀ (fun j=>d.R₀ j.val.val.val) r :=
    hFacts.1
  have havoid : p.residual hε u L x.val=avoidSource r u := hFacts.2.1
  have hcolumns : sourceColumns r=sourceColumns (p.residual hε u L x.val) := rfl
  have hprofile : commonProfile r degree control d.t₀ d.V tp=
      commonProfile d.root degree control d.t₀ d.V tp := rfl
  have hshape (en ee ez : ℝ) : fullShape r σ u seed p.scale Z en ee ez 40=
      fullShape (p.residual hε u L x.val) σ u seed p.scale Z en ee ez 40 := rfl
  have hb:=actual_bounds p hε (hcard k) hevent hWs u hu hucap L x
  have hcommon:=common_norm_caps M H hH d (hcard k) hevent.dimension p.label
  have hfrozen:=residual_frozen_caps M H hH d (hcard k) hevent p.label.val.1 hcommon.1
    p.allocation u L (p.selection hε L) x.val (Finset.mem_filter.mp x.property).2.2
  have htau:=first_modulus_cap M H hH d (hcard k) hevent.dimension hevent.presentation
    p.label p.inactive p.tau p.modulus
  have hσcap:=linear_sigma_cap hevent p.tau σ (frozenProduct q x.val) htau hfrozen.1 hσ
  have hradius0 : 0≤p.radius hε u L x.val := by
    change 0≤p.cutoff hε u L x.val*Z^(cutoffLoss N ε/2)
    exact (mul_pos hb.cutoffPos (Real.rpow_pos_of_pos (zero_lt_one.trans d.one_lt_Z) _)).le
  have hfamily:=plain_family_cap hevent (p.residual hε u L x.val) σ (p.radius hε u L x.val)
    hσcap hfrozen.2.1 hb.poolCap hradius0 hb.radiusCap
  have hholes : r.H=∅ := by change d.root.H=∅; exact d.hH
  have hholeprod : ((∏I∈MixedCompletedRows.holes r.H,I).absNorm:ℝ)≤Z^(0:ℝ) := by
    simp [hholes,MixedCompletedRows.holes]
  have hnorm8 : sourceNormCap r.P (9/4) r.T r.d≤Z^(8:ℝ) :=
    hb.sharpCap.trans (Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by norm_num))
  have hK16 : p.scale≤Z^(16:ℝ) :=
    hb.radialCap.trans (Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by norm_num))
  have hT16 : p.cutoff hε u L x.val≤Z^(16:ℝ) :=
    hb.cutoffCap.trans (Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le (by norm_num))
  have hcut : (sourceNormCap r.P (9/4) r.T r.d)^2/p.scale≤p.cutoff hε u L x.val := by
    change _≤secondSourceCutoff (p.residual hε u L x.val) p.scale
    rw [secondSourceCutoff,envelope_eq_normcap]
    exact le_rfl
  have hbound:=hbase.2 i (fun j=>d.chars j.val.val.val) (fun j=>d.w j.val.val.val)
    (fun _=>33/50) (fun j=>d.freq j.val.val.val) d.t₀ d.V (fun j=>d.R₀ j.val.val.val)
    (fun j=>d.hw j.val.val.val) (fun j=>d.hwm j.val.val.val) (fun _=>le_rfl) (fun _=>le_rfl)
    d.hV (fun j=>d.hfreq j.val.val.val) (fun j=>d.hholes j.val.val.val) hadmit.2.1
    r hcan (fun j=>d.hM j.val.val.val) hfrozen.2.1
    (by rw [hholes]; exact Finset.empty_subset _) hholeprod
    (by intro j P hP; simp only [hholes,Finset.notMem_empty] at hP)
    d.hX₁ d.hX₂ d.hY₁ d.hY₂ hnorm8 hb.poolCap hb.holeCap hb.productCap
    (unavoided_enclosure p.source (by norm_num) p.cover u L (p.selection hε L) x.val)
    u seed hu.ne_zero hucap hb.seedSquarefree
    (actual_global_avoidance p.source (by norm_num) p.cover u L (p.selection hε L) x)
    σ tp p.scale (p.cutoff hε u L x.val) hb.radialPos hσcap
    (by simpa only [one_mul, Point.radius] using hb.radiusCap) hK16 hT16 hcut hfamily
  simp only [←havoid,hcolumns,hprofile,hshape] at hbound
  convert hbound using 1 <;>
    simp only [nativeLoss,exceptionalLoss,zeroLoss,seed,q] <;> try ring

end
end Candidate.FourthPower.RepairedSmallPoint

