/- Copyright (c) 2026 Sil. Apache-2.0.
Actual four-component RAW finite supplier bound on the large branch.
All analytic suppliers are invoked before moving first ideals/suppliers.
The first-live exceptional shape is deliberately retained for the genuine
first-allocation reference theorem.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedActualLargeRetained
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedPointCaps
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedExceptionalRawCost
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedRemainderRawCost
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.RepairedSupplierFourCost

set_option autoImplicit false
namespace Candidate.FourthPower.RepairedLargeSupplierBudget
universe u v
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open ActualEisensteinCubic ConcretePrimeRowBridge EisensteinSchwartzPoisson
open QRH.Record1252270103KernelMass
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow CenteredMomentSupportedTailAggregate
open CenteredMomentFiniteProfileExceptional CenteredMomentLattice
open MixedPrincipalPair MixedPrincipalAllocations MixedPrincipalWindow MixedOriginalTail
open MixedSupplierFourthRow MixedSupplierSource MixedSupplierPositive MixedSupplierOuterActive
open MixedSupplierOriginalFrequency MixedInnerExceptionalBlock MixedFirstExceptionalNormalization
open OuterFreshSource OuterFreshSelected OuterFreshConsumer OuterFreshCutoffAllowance
open RepairedRawContext RepairedFirstPoint RepairedPointCaps RepairedRootParameters RepairedRootCaps RepairedCapEvent
open RepairedRawReference RepairedRawSupplier RepairedGroupedConsumer RepairedComponentRawCost
open RepairedSupplierProfiles RepairedActualLargeRetained RepairedExceptionalRawCost RepairedRemainderRawCost
open RepairedSupplierFourCost
open ConcreteTraceCRT
open MixedPrincipalCentered
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {M : Id} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} {hH : RayOrthogonality.globalUnits M ≤ H}
variable {ι : Type u} [Fintype ι] {Wslot : ℝ → ℂ} {N Holes : ℕ} {ε Z Kslot : ℝ}
variable {η η₀ : Character} {d : RootInput M H hH ι Wslot N Holes ε Z Kslot η η₀}

-- Match the concrete instance used by the checked Point/PointCaps source
-- constructors before synthesizing their nested residual Fintype instances.
local instance (priority := 2000) (p : Point d) : DecidableEq p.Index := Classical.decEq _

structure Controls where
  nonexceptionalDegree : ℕ
  nonexceptionalControl : Finset (ℕ×ℕ)
  exceptionalDegree : ℕ
  exceptionalControl : Finset (ℕ×ℕ)

structure Constants where
  zero : ℝ
  nonexceptional : ℝ
  exceptional : ℝ
  tail : ℝ
  zero_pos : 0 < zero
  nonexceptional_pos : 0 < nonexceptional
  exceptional_pos : 0 < exceptional
  tail_pos : 0 < tail

def coefficientZero (p : Point d) (c : Constants) : ℝ :=
  c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap p.source)^2*
    (2:ℝ)^N*(9/4:ℝ)^2*p.scale*Z^(∑ i,d.w i)*(sourceVolume p.source/pairNorm p.source.d)*
    Z^(2*cutoffLoss N ε)
def coefficientNonexceptional (p : Point d) (U : Controls) (c : Constants) (tp : ℝ) : ℝ :=
  c.nonexceptional*(Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2)*
    profileCore p.source Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V*
    referenceBase p.tau p.label.val.1 (sourceVolume d.root)*Z^(windowLoss ε)
def coefficientExceptional (p : Point d) (U : Controls) (c : Constants) (tp : ℝ) : ℝ :=
  c.exceptional*selectedCap N Kslot*heightBase tp^(2*U.exceptionalDegree)*
    (profileEnvelope p.source N Kslot U.exceptionalDegree U.exceptionalControl Z (cutoffLoss N ε))^2*
    shape (sourceVolume p.source) (pairNorm p.source.d) (prefixNormMax p.source.d) p.source.L p.scale 1*
    Z^(17*cutoffLoss N ε)
def coefficientTail (p : Point d) (c : Constants) : ℝ :=
  c.tail*selectedCap N Kslot*(profileCap p.source)^2*Z^(-(40:ℝ))
def budget (p : Point d) (U : Controls) (c : Constants) (tp : ℝ) : ℝ :=
  256*(coefficientZero p c+coefficientNonexceptional p U c tp+
    coefficientExceptional p U c tp+coefficientTail p c)

theorem coefficients_nonneg (p : Point d) (U : Controls) (c : Constants) (tp : ℝ)
    (hKslot : 1 ≤ Kslot) :
    0 ≤ coefficientZero p c ∧ 0 ≤ coefficientNonexceptional p U c tp ∧
      0 ≤ coefficientExceptional p U c tp ∧ 0 ≤ coefficientTail p c := by
  have hz := zero_lt_one.trans d.one_lt_Z
  have hk : 0 < p.scale := Real.rpow_pos_of_pos hz _
  have hv := sourceVolume_pos p.source
  have hp := pairNorm_pos p.source.hd.1 p.source.hd.2
  have hh := prefixNormMax_pos p.source.d p.source.hd
  have hl := p.source.hL
  have hc := profileCore_nonneg p.source Kslot N U.nonexceptionalDegree U.nonexceptionalControl
    d.t₀ tp d.V (zero_le_one.trans hKslot) d.hV
  have hr := referenceBase_nonneg p.tau p.label.val.1 (sourceVolume d.root)
  have ht := heightBase_pos tp
  have hcz := c.zero_pos
  have hcn := c.nonexceptional_pos
  have hce := c.exceptional_pos
  have hct := c.tail_pos
  unfold coefficientZero coefficientNonexceptional coefficientExceptional coefficientTail selectedCap shape
  refine ⟨?_,?_,?_,?_⟩ <;> positivity

theorem selected_root_product (p : Point d) (hε : 0 < ε) (u : Id) (L : Finset p.Index) :
    selectedVolume (p.data hε u L) ≤ Z^(∑ i,d.w i) := by
  let q := p.data hε u L
  have h₁ : selectedVolume q ≤ ∏ i,p.source.P i :=
    injected_prod_le (fun j : q.J => j.val.val)
      (fun i j he => Subtype.ext (Subtype.ext he)) p.source.P p.source.hP
  have h₂ : (∏ i,p.source.P i) ≤ ∏ i,d.root.P i :=
    injected_prod_le (fun i : p.Index => i.val) Subtype.val_injective d.root.P d.root.hP
  exact (h₁.trans h₂).trans_eq (root_product M H hH d)

/-- Compact name for exactly the public finite supplier conclusion. -/
def Result (p : Point d) (hε : 0 < ε) (U : Controls) (c : Constants) : Prop :=
  ∀ u : Id, Squarefree u → (u.absNorm:ℝ) ≤ Z^(8:ℝ) →
  ∀ L : Finset p.Index, p.large L → ∀ x : activeFrozen (p.data hε u L),
  ∀ (tp : ℝ) (rows : Finset O),
    (∑ z ∈ rows,(ballProfile (‖eisEmbedding z‖^2/p.scale)).re*
      ‖MixedSupplierFourthRow.frozenWeight (p.data hε u L) x.val*
        originalFamily (p.data hε u L) x.val p.tau tp z‖^2) ≤
    budget p U c tp*rawSupplierCost (p.data hε u L) x.val (residualSeed (p.data hε u L) x)

/-- Scalar monotonicity only. Separating it avoids a positivity search
through the full dependent original supplier expression. -/
private theorem zero_coefficient_le (p : Point d) (hε : 0 < ε) (c : Constants)
    (hKslot : 1 ≤ Kslot) (u : Id) (L : Finset p.Index)
    (x : activeFrozen (p.data hε u L)) (seed : Id) :
    (c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap p.source)^2*
      (2:ℝ)^N*(9/4:ℝ)^2*p.scale*selectedVolume (p.data hε u L)*
      (sourceVolume p.source/pairNorm p.source.d)*Z^(2*cutoffLoss N ε))*
        rawSupplierCost (p.data hε u L) x.val seed ≤
      coefficientZero p c*rawSupplierCost (p.data hε u L) x.val seed := by
  let q := p.data hε u L
  let F := c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap p.source)^2*
    (2:ℝ)^N*(9/4:ℝ)^2*p.scale
  let T := (sourceVolume p.source/pairNorm p.source.d)*Z^(2*cutoffLoss N ε)
  change (c.zero*selectedCap N Kslot*‖paperRadialFourier ballProfile 0‖*(profileCap p.source)^2*
    (2:ℝ)^N*(9/4:ℝ)^2*p.scale*selectedVolume q*(sourceVolume p.source/pairNorm p.source.d)*
      Z^(2*cutoffLoss N ε))*rawSupplierCost q x.val seed ≤
    coefficientZero p c*rawSupplierCost q x.val seed
  have hZ := zero_lt_one.trans d.one_lt_Z
  have hK : 0 < p.scale := Real.rpow_pos_of_pos hZ _
  have hKslot0 : 0 ≤ Kslot := zero_le_one.trans hKslot
  have hC := c.zero_pos
  have hF : 0 ≤ F := by dsimp only [F,selectedCap]; positivity
  have hT : 0 ≤ T := mul_nonneg
    (div_nonneg (sourceVolume_pos p.source).le (pairNorm_pos p.source.hd.1 p.source.hd.2).le)
    (Real.rpow_nonneg hZ.le (2*cutoffLoss N ε))
  have hqP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (p.source.hP i)
  have hc := rawSupplierCost_nonneg q hqP x.val seed
  have hvol : selectedVolume q ≤ Z^(∑ i,d.w i) := selected_root_product p hε u L
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol hF) hT) hc
  convert he using 1 <;> first | rfl | (dsimp only [F,T,coefficientZero]; ring)

/-- Consumes the already proved retained estimate. The uniform theorem
below supplies that estimate internally, so this is only a normalization
helper and does not add an input to the public endpoint. -/
private theorem retained_raw_cost (p : Point d) (hε : 0 < ε) (U : Controls) (c : Constants)
    (Q : Id) (hKslot : 1 ≤ Kslot) (hcard : Fintype.card p.Index ≤ N)
    (hslots : ∀ i,p.source.M i ≤ Kslot)
    (hret : RetainedBound p hε U.nonexceptionalDegree U.nonexceptionalControl c.nonexceptional Q)
    (u : Id) (L : Finset p.Index) (hL : p.large L) (x : activeFrozen (p.data hε u L))
    (hseed : Squarefree (residualSeed (p.data hε u L) x)) (ξ : RayCharacter) (tp : ℝ) :
    supplierFront (p.data hε u L) x.val *
      ‖selectedSum (p.data hε u L) x.val p.tau
        (fun y => fixedPart false (p.data hε u L) x.val y (p.residual hε u L x.val)
          (residualSeed (p.data hε u L) x) p.tau ξ 1 Q tp ballProfile p.scale
          (p.cutoff hε u L x.val) Z (cutoffLoss N ε) (Z^(8:ℝ)))‖ ≤
      coefficientNonexceptional p U c tp*rawSupplierCost (p.data hε u L) x.val
        (residualSeed (p.data hε u L) x) := by
  let q := p.data hε u L
  let r := p.residual hε u L x.val
  let seed := residualSeed q x
  change supplierFront q x.val *
    ‖selectedSum q x.val p.tau (fun y => fixedPart false q x.val y r seed p.tau ξ 1 Q tp ballProfile
      p.scale (p.cutoff hε u L x.val) Z (cutoffLoss N ε) (Z^(8:ℝ)))‖ ≤
    coefficientNonexceptional p U c tp*rawSupplierCost q x.val seed
  have hqP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (p.source.hP i)
  have hx := (Finset.mem_filter.mp x.property).2.2
  have hbound := hret u L hL x.val hx seed hseed (residualSeed_spec q x) ξ 1 tp
  have hp := residual_rawProfileRoot p.source (by norm_num) p.cover u L (p.selection hε L) x.val
    N hcard Kslot hKslot hslots
  have hp' : rawProfileRoot r ≤ Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2 := hp
  have hprof : profileCore r Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V =
      profileCore p.source Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V := rfl
  have hcore := profileCore_nonneg p.source Kslot N U.nonexceptionalDegree U.nonexceptionalControl
    d.t₀ tp d.V (zero_le_one.trans hKslot) d.hV
  have href := firstReference_nonneg q hqP p.tau p.label.val.1 (sourceVolume d.root)
  have hscale := (MixedSelectedVolume.scale_pos q hqP).le
  have hZ := zero_lt_one.trans d.one_lt_Z
  have hmono := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp' href) hcore)
        (mul_nonneg c.nonexceptional_pos.le hscale))
      (Real.rpow_nonneg hZ.le (windowLoss ε))) (Nat.cast_nonneg seed.absNorm)
  rw [hprof] at hbound
  have hcoarse : ‖selectedSum q x.val p.tau
      (fun y => fixedPart false q x.val y r seed p.tau ξ 1 Q tp ballProfile p.scale
        (p.cutoff hε u L x.val) Z (cutoffLoss N ε) (Z^(8:ℝ)))‖ ≤
      (c.nonexceptional*(Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2)*
        profileCore p.source Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V*Z^(windowLoss ε))*
        (MixedSelectedVolume.scale q*firstReference q p.tau p.label.val.1 (sourceVolume d.root)/(seed.absNorm:ℝ)) := by
    apply (hbound.trans hmono).trans_eq
    ring
  have hid := raw_supplier_reference_identity q x.val seed p.tau p.label.val.1 (sourceVolume d.root)
  change supplierFront q x.val*(MixedSelectedVolume.scale q*firstReference q p.tau p.label.val.1
    (sourceVolume d.root)/(seed.absNorm:ℝ)) = _ at hid
  apply (mul_le_mul_of_nonneg_left hcoarse (supplierFront_nonneg q x.val)).trans_eq
  calc
    _ = (c.nonexceptional*(Kslot^(4*N)*(2:ℝ)^N/(1/4:ℝ)^2)*
        profileCore p.source Kslot N U.nonexceptionalDegree U.nonexceptionalControl d.t₀ tp d.V*Z^(windowLoss ε))*
        (supplierFront q x.val*(MixedSelectedVolume.scale q*firstReference q p.tau p.label.val.1
          (sourceVolume d.root)/(seed.absNorm:ℝ))) := by ring
    _ = _ := by rw [hid]; unfold coefficientNonexceptional; ring

/-- This endpoint has no energy estimate premise. It supplies the
literal finite supplier at the actual chosen large block. Its RHS still
displays first geometry, to be paid by first allocation/reference. -/
private theorem uniform_large_supplier_result
    (Index : Type v) [Fintype Index] (RootSlot : Index → Type u) [∀ k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀ k,Fintype.card (RootSlot k) ≤ N) (ε : ℝ) (hε : 0 < ε)
    (Wslot : ℝ → ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot ⊆ Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1 ≤ Kslot) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M)
    (η η₀ : Character) (hQη₀ : Q ≤ η₀.modulus) :
    ∃ U : Controls, ∃ c : Constants, ∀ᶠ Z : ℝ in atTop,
    ∀ k : Index, ∀ d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀ p : Point d, Result p hε U c := by
  have hδ := (internal_losses_paid N ε hε).1
  have hgap : (2/3:ℝ)+2*cutoffLoss N ε < 1 := by
    have hi := (internal_spec N ε hε).2.2.1
    have ho := (omega_spec ε hε).2.2.2
    unfold cutoffLoss
    linarith
  obtain ⟨dn,Sn,Cn,hCn,hn⟩ := uniform_actual_large_retained (M:=M) (H:=H) (hH:=hH) Index RootSlot N Holes hcard
    ε hε Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀
  obtain ⟨de,Se,h00,Ce,hCe,he⟩ := uniform_exceptional_raw_cost N (2/3) 64 (1/4) (9/4)
    (cutoffLoss N ε) (cutoffLoss N ε) 8 15 1 (cutoffLoss N ε)
    le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) hδ hδ hgap
    (by norm_num) (by norm_num) (by norm_num) hδ Q (NeZero.ne Q) hQt hQ72
  obtain ⟨Cz,hCz,hz⟩ := uniform_zero_raw_cost N (cutoffLoss N ε) hδ
  obtain ⟨Ct,hCt,ht⟩ := uniform_tail_raw_cost N 16 10 (cutoffLoss N ε) 40 (by norm_num) hδ
  let U : Controls := ⟨dn,Sn,de,Se⟩
  let c : Constants := ⟨Cz,Cn,Ce,Ct,hCz,hCn,hCe,hCt⟩
  refine ⟨U,c,?_⟩
  filter_upwards [hn,he,ht,eventually_event.{u} N ε hε] with Z hn he ht hevent
  intro k d p u hu hucap L hL x tp rows
  let q := p.data hε u L
  let r := p.residual hε u L x.val
  let seed := residualSeed q x
  have caps := actual_bounds p hε (hcard k) hevent hWs u hu hucap L x
  have hP : ∀ i,0 < q.P i := fun i => zero_lt_one.trans_le (p.source.hP i)
  have hx := (Finset.mem_filter.mp x.property).2.2
  have hcost := rawSupplierCost_nonneg q hP x.val seed
  have hcoef := coefficients_nonneg p U c tp hKslot
  have hzero (ξ : RayCharacter) : supplierFront q x.val *
      ‖selectedSum q x.val p.tau (fun y => outerZero q x.val y r seed p.tau ξ tp p.scale)‖ ≤
        coefficientZero p c*rawSupplierCost q x.val seed := by
    have hh := hz p.Index (1/4) (9/4) p.source (by norm_num) p.cover caps.card Kslot hKslot caps.slots
      u L (p.selection hε L) x.val seed caps.seedSquarefree.ne_zero p.tau ξ tp p.scale Z 2
      caps.radialPos.le d.one_lt_Z caps.sharpCap
    exact hh.trans (zero_coefficient_le p hε c hKslot u L x seed)
  have hnonexceptional (ξ : RayCharacter) : supplierFront q x.val *
      ‖selectedSum q x.val p.tau (fun y => fixedPart false q x.val y r seed p.tau ξ 1 Q tp ballProfile
        p.scale (p.cutoff hε u L x.val) Z (cutoffLoss N ε) (Z^(8:ℝ)))‖ ≤
        coefficientNonexceptional p U c tp*rawSupplierCost q x.val seed := by
    exact retained_raw_cost p hε U c Q hKslot caps.card caps.slots (hn k d p)
      u L hL x caps.seedSquarefree ξ tp
  have hexceptional (ξ : RayCharacter) : supplierFront q x.val *
      ‖selectedSum q x.val p.tau (fun y => fixedPart true q x.val y r seed p.tau ξ 1 Q tp ballProfile
        p.scale (p.cutoff hε u L x.val) Z (cutoffLoss N ε) (Z^(8:ℝ)))‖ ≤
        coefficientExceptional p U c tp*rawSupplierCost q x.val seed := by
    have hh := he.2 p.Index p.source p.cover caps.card Kslot hKslot caps.slots caps.slotSupport
      u L (p.selection hε L) x.val caps.holeCap caps.productCap caps.poolCap seed p.tau ξ 1
      caps.seedSquarefree caps.seedSquarefree.ne_zero tp p.scale (p.cutoff hε u L x.val)
      (cutoffLoss N ε) (Z^(8:ℝ)) caps.radialPos caps.cutoffPos.le caps.poolCap le_rfl
      (by simpa only [one_mul,Point.radius] using caps.radiusCap)
      (by
        intro y hy
        convert caps.familyCap y hy using 1 <;> rfl)
    have hexp : 2*(8:ℝ)*cutoffLoss N ε+cutoffLoss N ε = 17*cutoffLoss N ε := by ring
    rw [hexp] at hh
    convert hh using 1 <;> first | rfl | (dsimp only [coefficientExceptional,U,c,q,r,seed]; ring)
  have htail (ξ : RayCharacter) : supplierFront q x.val *
      ‖selectedSum q x.val p.tau (fun y => secondDiscardedEnergy p.tau tp (sourceColumns r)
        (outerColumn q x.val y seed ξ) ballProfile p.scale (p.cutoff hε u L x.val) Z (cutoffLoss N ε))‖ ≤
        coefficientTail p c*rawSupplierCost q x.val seed := by
    have hmon (a : ℝ) (ha : a ≤ 16) : Z^a ≤ Z^(16:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le d.one_lt_Z.le ha
    have hh := ht.2 p.Index (1/4) (9/4) p.source (by norm_num) (by norm_num) p.cover caps.card Kslot hKslot caps.slots
      u L (p.selection hε L) x.val seed caps.seedSquarefree.ne_zero caps.rawRatioCap ξ p.tau tp p.scale
      (secondSourceEnvelope r) (p.cutoff hε u L x.val) caps.radialPos caps.envelopePos
      (caps.poolCap.trans (hmon 8 (by norm_num)))
      (RepairedRootCaps.envelope_eq_normcap r).symm.le
      (caps.envelopeCap.trans (hmon 2 (by norm_num))) (caps.radialCap.trans (hmon 9 (by norm_num)))
      (caps.cutoffCap.trans (hmon 14 (by norm_num))) le_rfl
    exact hh
  exact finite_supplier_of_four q hP x r (by norm_num)
    (residual_matches p.source (by norm_num) p.cover u L (p.selection hε L) x.val)
    p.tau 1 Q tp p.scale (p.cutoff hε u L x.val) Z (cutoffLoss N ε) (Z^(8:ℝ)) rows caps.radialPos caps.fixedPoolCap
    (coefficientZero p c) (coefficientNonexceptional p U c tp) (coefficientExceptional p U c tp) (coefficientTail p c)
    hcoef.1 hcoef.2.1 hcoef.2.2.1 hcoef.2.2.2 hzero hnonexceptional hexceptional htail

/-- Public statement is literally unchanged; only its implementation is
split through the compact Result and the proved scalar helpers above. -/
theorem uniform_large_supplier_cost
    (Index : Type v) [Fintype Index] (RootSlot : Index → Type u) [∀ k,Fintype (RootSlot k)]
    (N Holes : ℕ) (hcard : ∀ k,Fintype.card (RootSlot k) ≤ N) (ε : ℝ) (hε : 0 < ε)
    (Wslot : ℝ → ℂ) (hW : ContDiff ℝ ∞ Wslot) (hWs : Function.support Wslot ⊆ Icc (1:ℝ) 2)
    (Kslot : ℝ) (hKslot : 1 ≤ Kslot) (hβ : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (Q : Id) [NeZero Q] (hQt : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)}) (hQM : Q ≤ M)
    (η η₀ : Character) (hQη₀ : Q ≤ η₀.modulus) :
    ∃ U : Controls, ∃ c : Constants, ∀ᶠ Z : ℝ in atTop,
    ∀ k : Index, ∀ d : RootInput M H hH (RootSlot k) Wslot N Holes ε Z Kslot η η₀,
    ∀ p : Point d, ∀ u : Id, Squarefree u → (u.absNorm:ℝ) ≤ Z^(8:ℝ) →
    ∀ L : Finset p.Index, p.large L → ∀ x : activeFrozen (p.data hε u L),
    ∀ (tp : ℝ) (rows : Finset O),
      (∑ z ∈ rows,(ballProfile (‖eisEmbedding z‖^2/p.scale)).re*
        ‖MixedSupplierFourthRow.frozenWeight (p.data hε u L) x.val*
          originalFamily (p.data hε u L) x.val p.tau tp z‖^2) ≤
      budget p U c tp*rawSupplierCost (p.data hε u L) x.val (residualSeed (p.data hε u L) x) := by
  exact uniform_large_supplier_result Index RootSlot N Holes hcard ε hε
    Wslot hW hWs Kslot hKslot hβ Q hQt hQ72 hQM η η₀ hQη₀

end
end Candidate.FourthPower.RepairedLargeSupplierBudget
