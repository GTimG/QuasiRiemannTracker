/- Copyright (c) 2026 Sil. Apache-2.0.
The actual allocated outer window: canonical provenance and the uniform
seeded estimate are supplied internally. Full punctures, enlarged ordinary
prefixes and the live/original normalization ratio remain explicit.
The actual numerical gates and final outer summation remain explicit duties.
-/
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstOuterUniformity
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.OuterFreshDeclaredRadius
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedFirstSourceGeometry
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedOriginalTailCaps
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedOriginalCoprimality
import Submissions.runbo_li_arvi_face_8746074_20261026.FourthPower.MixedInnerExceptionalLedger

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Candidate.FourthPower.OuterFreshAllocatedWindow
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CompletedGauss (primaryGenerator)
open QRH.Record1252270103KernelMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonProfile
open CenteredMomentCommonAllocationSum CenteredMomentCommonAllocationBox
open CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentSourceLiveColumn CenteredMomentSectorLocalization
open CenteredMomentFirstPhysicalSource
open CenteredMomentSourceRow CenteredMomentActiveSource CenteredMomentSecondBlockAggregate
open CenteredMomentSecondHeightFamily CenteredMomentFirstAmplificationChoice
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open CenteredMomentFiniteProfileExceptional CenteredMomentUncenteredTerminal
open CenteredExceptionalProfile CenteredMomentSecondScaled
open MixedPrincipalPair MixedPrincipalWindow MixedPrincipalAllocations
open MixedCommonCoefficient MixedCommonRestriction MixedLiteralAllocation MixedLiveNormalization
open MixedInnerExceptionalBlock MixedInnerExceptionalLedger
open MixedFirstPhysicalApplication MixedFirstSeededEnergy MixedFirstSourceWindow
open MixedFirstOuterUniformity MixedFirstSourceMoment MixedFirstProfileEnvelope
open MixedFirstUniformLossBudget MixedFirstChosenEnergy MixedFirstReferenceChoice
open MixedFirstActualNonexceptional MixedFirstLiveSource MixedFirstSourceGeometry
open MixedSupplierFourthRow MixedSupplierPositive MixedSupplierSource
open MixedCanonicalSource ReferencePrimeEnclosure MixedOriginalNormCap
open OuterFreshSource OuterFreshSelectedWindow OuterFreshConsumer OuterFreshDeclaredRadius
open OuterFreshWindowPair
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {α : Type*} : DecidableEq α := Classical.decEq _
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-- The seed of the actual fixed label survives genuine extraction.
Its support is obtained from the actual commonColumn/source identity. -/
theorem fixed_label_seed (s : Source ι a b) (ha : 0<a) (cover : OriginalEnclosure s)
    (u : Id) (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed : Id) (hseed : Squarefree seed)
    (p : FixedLabel (fixedPool (supplierData s ha u L J) x
      (residualSource s ha cover u L J x) seed)) :
    seed∣p.val.1 ∧ seed∣p.val.2 := by
  apply MixedOriginalCoprimality.active_common_seed
    (sourceColumns (residualSource s ha cover u L J x))
    (commonColumn (supplierData s ha u L J) x seed) seed hseed _ p
  intro I hI
  have hc := common_coefficient (supplierData s ha u L J) x
    (residualSource s ha cover u L J x) ha (residual_matches s ha cover u L J x) seed I
  rw [hc] at hI
  exact source_coefficient_seed (residualSource s ha cover u L J x) ha seed I
    (mul_ne_zero_iff.mp hI).2

set_option maxHeartbeats 600000 in
/-- The actual avoided window has exactly the same live polynomial after
supplier/genuine extraction. The radial majorant is inserted only on its
actual finite disk, with the original selected family and keep unchanged. -/
theorem actual_finite_window_eq (s : Source ι a b) (ha : 0<a)
    (hb : 0≤b) (cover : OriginalEnclosure s) (u : Id)
    (L : Finset ι) (J : Finset {i // i∉Lᶜ})
    (x : Frozen (supplierData s ha u L J)) (seed G : Id)
    (hu : u=frozenProduct (supplierData s ha u L J) x*seed) (hseed : seed∣G)
    (Balloc : actualAllocations (tuplePools (unavoidedResidual s ha cover u L J x)) G)
    (D : Id) (η : Character) (tp : ℝ) (keep : Id→O→Prop)
    (Z Rdecl : ℝ) (hZ : 0<Z) (Vwin : ℝ→ℂ) (X θwin : ℝ) (rows : Finset O)
    (hrows : ∀z∈rows,normValue z≤paddedRadius η Z Rdecl) :
    let q:=supplierData s ha u L J
    let r:=unavoidedResidual s ha cover u L J x
    let live:=allocatedLiveSource r hb cover G Balloc
    let actual:=allocatedLiveSource (residualSource s ha cover u L J x) hb cover G Balloc
    (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
      ∑z∈rows,if keep F.val z then
        ‖windowedPolynomial actual ha D F.val η fixedBadMask 1 tp Vwin X θwin z‖^2 else 0)/
        sourceVolume live=
    seededGroupedWindowRows q live ha D η tp keep ballProfile (paddedRadius η Z Rdecl)
      Vwin X θwin rows := by
  dsimp only
  refine Eq.trans ?_ (finite_window_eq_padded (supplierData s ha u L J)
    (allocatedLiveSource (unavoidedResidual s ha cover u L J x) hb cover G Balloc)
    ha D η tp keep Z Rdecl hZ Vwin X θwin rows hrows)
  apply congrArg (fun v : ℝ=>v/sourceVolume
    (allocatedLiveSource (unavoidedResidual s ha cover u L J x) hb cover G Balloc))
  apply Finset.sum_congr rfl
  intro F hF
  apply congrArg (fun v : ℝ=>(groupedWeight (supplierData s ha u L J) F.val/
    MixedSelectedVolume.scale (supplierData s ha u L J))*v)
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hk : keep F.val z
  · simp only [if_pos hk]
    exact congrArg (fun v : ℂ=>‖v‖^2)
      (actual_allocated_window s ha hb cover u L J x seed G hu hseed Balloc
        D F.val η fixedBadMask 1 tp Vwin X θwin z)
  · simp only [if_neg hk]

/-- Full fixed-label norm cap after absorption of the fixed lattice
constant. It comes from the original source support, not a radical. -/
def commonExponent (Lorig Nslot Lslot : ℝ) : ℝ := 2*Lorig+Nslot*Lslot+1

def punctureExponent (BR0 Lorig Nslot Lslot B : ℝ) : ℝ :=
  BR0+B+commonExponent Lorig Nslot Lslot

variable (M : Id) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (Hray : Subgroup (O⧸M)ˣ) (hHray : RayOrthogonality.globalUnits M≤Hray)

set_option maxHeartbeats 600000 in
/-- An actual fixed common label and genuine allocation, including the
original normalization and frozen coefficient. Only scalar declared-width,
capacity and actual disk gates remain as caller inputs. The canonical
source estimate and every inherited support/norm/profile fact are supplied
by the theorem, not postulated as an energy or Source-estimate premise. -/
theorem uniform_actual_allocated_window
    (Vwin : ℝ→ℂ) (hVc : HasCompactSupport Vwin) (hVs : ContDiff ℝ ∞ Vwin)
    (N Holes : ℕ) (hcard : Fintype.card ι≤N) (Wslot : ℝ→ℂ)
    (a b Lorig B Lslot Lcap Cap BR0 BH Bη lo hi Kslot Bseed ε rho : ℝ)
    (hWs : Function.support Wslot⊆Set.Icc (1:ℝ) 2) (hW : ContDiff ℝ ∞ Wslot)
    (ha : 0<a) (haUpper : a≤1/4) (hb : 1≤b)
    (hLorig : 0≤Lorig) (hB : 2*Lorig+1≤B)
    (hLslot : 0≤Lslot) (hLcap : Lslot≤Lcap) (hBcap : B≤Lcap)
    (hslots : (N:ℝ)*Lslot+1≤B) (hCap : 2≤Cap) (hCapc : b/comparisonScale b≤Cap)
    (hBR0 : 0≤BR0) (hBH : 0≤BH) (hBη : 0≤Bη) (hηB : Bη+1≤B)
    (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hKslot : 1≤Kslot)
    (hBseed : 0≤Bseed) (hε : 0<ε) (hrho : 0<rho)
    (Q : Id) [NeZero Q] (hQt : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQM : Q≤M) :
    let step:=budgetStep B Bseed ε rho
    ∃degree : ℕ,∃control : Finset (ℕ×ℕ),∀η₀ : Character,Q≤η₀.modulus→
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,1<Z ∧
    ∀(θ : ι→RayQuotient.Characters M Hray)(w σ freq : ι→ℝ)
      (t₀ tp V : ℝ)(R₀ : ι→Finset Id),
      (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
      0≤V→(∀i,|freq i|≤V)→(∀i,(R₀ i).card≤Holes)→
    ∀s : Source ι a b,Canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀ s→
      (∀i,s.M i≤Kslot)→(s.R.absNorm:ℝ)≤Z^BR0→
      s.H⊆enclosure (Cap*Z^Lcap)→((∏I∈MixedCompletedRows.holes s.H,I).absNorm:ℝ)≤Z^BH→
      (∀i,∀P∈s.H,P.val∈R₀ i)→(s.Fhole.absNorm:ℝ)≤Z^BH→
      s.X₁≤Z^Lorig→s.X₂≤Z^Lorig→s.Y₁≤Z^Lorig→s.Y₂≤Z^Lorig→
    ∀cover : OriginalEnclosure s,∀u : Id,∀L : Finset ι,∀J : Finset {i // i∉Lᶜ},
    let q:=supplierData s ha u L J
    ∀x : Frozen q,MixedSupplierFourthRow.frozenWeight q x≠0→
    ∀seed : Id,Squarefree seed→u=frozenProduct q x*seed→
    ∀p : FixedLabel (fixedPool q x (residualSource s ha cover u L J x) seed),
    ∀G : Id,G=p.val.1 ∨ G=p.val.2→
    let r:=unavoidedResidual s ha cover u L J x
    ∀Balloc : actualAllocations (tuplePools r) G,
    let live:=allocatedLiveSource r (zero_le_one.trans hb) cover G Balloc
    let actual:=allocatedLiveSource (residualSource s ha cover u L J x)
      (zero_le_one.trans hb) cover G Balloc
    let cactual:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Balloc.val*
      frozenCoefficient Balloc.val G r.R (residualSource s ha cover u L J x).ν r.Wslot r.P
    let ccanonical:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Balloc.val*
      frozenCoefficient Balloc.val G r.R r.ν r.Wslot r.P
    ∀η : Character,(η.modulus.absNorm:ℝ)≤Z^Bη→
    ∀Rdecl : ℝ,0≤Rdecl→Rdecl≤B→
    ∀(χ₀ : RayCharacter)(msecond : O),msecond≠0→goodLambda∣msecond→(2:O)∣msecond→
    let P:=Real.logb Z (s.T/pairNorm (s.d.1*Balloc.val (Sum.inr 0),s.d.2*Balloc.val (Sum.inr 1)))
    let S:=∑i : liveIndices Balloc.val,w i.val.val.val
    let d:=Real.logb Z (MixedSelectedVolume.volume q)
    P+2*S+4*d≤Rdecl-rho→(3/4:ℝ)*S<d→
    ∀keep : Id→O→Prop,
      (∀F∈selectedProducts q,∀z,keep F z→z≠0)→
      (∀F∈selectedProducts q,∀z,keep F z→
        ¬FixedInducingRow η Q fixedBadMask ((primaryGenerator F)^2) z)→
    ∀D : Id,Squarefree D→(D.absNorm:ℝ)≤Z^Bseed→
    ∀X θwin : ℝ,0<X→∀rows : Finset O,
      (∀z∈rows,normValue z≤paddedRadius η Z Rdecl)→
    let E:=C*Kslot^(2*N)*(∏i : liveIndices Balloc.val,s.M i.val.val.val)^2*
      (sourceControl control s.W₁*sourceControl control s.W₂)^2*
      (height t₀ V s.t₁ s.t₂)^degree*heightCost tp θwin^(2*degree)*
      (∫v : ℝ,(1+‖v‖)^degree*‖columnDensity Vwin hVc hVs v‖)^2*
      (Z^Rdecl/fixedPresentationCost)*Z^ε
    Z^step*‖normalization (r.X₁*r.X₂) r.P‖^2*‖cactual‖^2*
      (∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
        ∑z∈rows,if keep F.val z then
          ‖windowedPolynomial actual ha D F.val η fixedBadMask 1 tp Vwin X θwin z‖^2 else 0)≤
      (‖ccanonical‖^2*((∏i : liveIndices Balloc.val,r.P i.val)/(∏i,r.P i))*E)/
        (pairNorm (s.d.1*Balloc.val (Sum.inr 0),s.d.2*Balloc.val (Sum.inr 1))*(D.absNorm:ℝ)) := by
  dsimp only
  let BRlive:=punctureExponent BR0 Lorig (N:ℝ) Lslot B
  have hB0 : 0≤B := by linarith
  have hBRlive : 0≤BRlive := by
    dsimp only [BRlive,punctureExponent,commonExponent]
    positivity
  obtain ⟨degree,control,hbase⟩ := uniform_seeded_rest_window (ι:=ι) M Hray hHray
    Vwin hVc hVs ballProfile N Holes hcard Wslot a b Lorig B Lslot Lcap Cap BRlive BH Bη
    lo hi Kslot Bseed ε rho CenteredMomentEnergyChildState.ball_support
    (fun x=>ballProfile_nonneg x) hWs hW ha haUpper hb hLorig hB hLslot hLcap hBcap
    (by linarith) hCap hCapc hBRlive hBH hBη hβ hKslot hBseed hε hrho Q hQt hQ72 hQM
  refine ⟨degree,control,?_⟩
  intro η₀ hη₀
  obtain ⟨C,hC,hbase⟩ := hbase η₀ hη₀
  have hnorm := MixedOriginalTailCaps.eventually_source_caps N b Lorig ((N:ℝ)*Lslot) 1 (by norm_num)
  have hpadded := padded_caps_eventually 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hbase,hnorm,hpadded,eventually_ge_atTop ((2:ℝ)^N)] with Z hbaseZ hnormZ hpaddedZ h2N
  have hZ : 1<Z := hbaseZ.1
  have hz : 0<Z := zero_lt_one.trans hZ
  refine ⟨hZ,?_⟩
  intro θ w σ freq t₀ tp V R₀ hw hwL hσ hσhi hV hfreq hR₀ s hcanonical hMs
    hR hHholes hholes hHR hFhole hX₁ hX₂ hY₁ hY₂ cover u L J x hx seed hseed hu p G hG
    Balloc η hη Rdecl hRdecl hRcap χ₀ msecond hm hml hm2 hmixed hnative
    keep hkeep heligible D hD hDcap X θwin hX rows hrows
  let q:=supplierData s ha u L J
  let r:=unavoidedResidual s ha cover u L J x
  let live:=allocatedLiveSource r (zero_le_one.trans hb) cover G Balloc
  let actual:=allocatedLiveSource (residualSource s ha cover u L J x)
    (zero_le_one.trans hb) cover G Balloc
  let cactual:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Balloc.val*
    frozenCoefficient Balloc.val G r.R (residualSource s ha cover u L J x).ν r.Wslot r.P
  let ccanonical:=MixedCommonCoefficient.frozenWeight (punctureProduct r.S r.H) Balloc.val*
    frozenCoefficient Balloc.val G r.R r.ν r.Wslot r.P
  let E:=C*Kslot^(2*N)*(∏i : liveIndices Balloc.val,s.M i.val.val.val)^2*
    (sourceControl control s.W₁*sourceControl control s.W₂)^2*
    (height t₀ V s.t₁ s.t₂)^degree*heightCost tp θwin^(2*degree)*
    (∫v : ℝ,(1+‖v‖)^degree*‖columnDensity Vwin hVc hVs v‖)^2*
    (Z^Rdecl/fixedPresentationCost)*Z^ε
  let raw:=∑F : selectedProducts q,(groupedWeight q F.val/MixedSelectedVolume.scale q)*
    ∑z∈rows,if keep F.val z then
      ‖windowedPolynomial actual ha D F.val η fixedBadMask 1 tp Vwin X θwin z‖^2 else 0
  change Z^(budgetStep B Bseed ε rho)*‖normalization (r.X₁*r.X₂) r.P‖^2*‖cactual‖^2*raw≤
    (‖ccanonical‖^2*((∏i : liveIndices Balloc.val,r.P i.val)/(∏i,r.P i))*E)/
      (pairNorm (s.d.1*Balloc.val (Sum.inr 0),s.d.2*Balloc.val (Sum.inr 1))*(D.absNorm:ℝ))
  have hproduct := (canonical_product M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀
    s hcanonical N Lslot ((N:ℝ)*Lslot) hZ hcard hLslot hw hwL le_rfl).2.2
  have hsourceCap : sourceNormCap s.P b s.T s.d≤Z^(commonExponent Lorig (N:ℝ) Lslot) :=
    (hnormZ.2 ι a s hcard hX₁ hX₂ hY₁ hY₂ hproduct).2
  have hGnorm : (G.absNorm:ℝ)≤Z^(commonExponent Lorig (N:ℝ) Lslot) := by
    have hh:=actual_fixed_common_norm_caps s ha cover u L J x seed p
    rcases hG with rfl|rfl
    · exact hh.1.trans hsourceCap
    · exact hh.2.trans hsourceCap
  have hprod2 : (∏i,2*s.P i)≤Z^B := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
    calc
      _≤(2:ℝ)^N*Z^((N:ℝ)*Lslot) :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hcard) hproduct
          (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))) (by positivity)
      _≤Z*Z^((N:ℝ)*Lslot) := mul_le_mul_of_nonneg_right h2N (Real.rpow_nonneg hz.le _)
      _=Z^((N:ℝ)*Lslot+1) := by rw [Real.rpow_add hz,Real.rpow_one];ring
      _≤Z^B := Real.rpow_le_rpow_of_exponent_le hZ.le hslots
  have hRlive : (live.R.absNorm:ℝ)≤Z^BRlive := by
    have hh:=allocated_puncture_norm s ha (zero_le_one.trans hb) cover u L J x hx G Balloc
    calc
      _≤(s.R.absNorm:ℝ)*(∏i,2*s.P i)*(G.absNorm:ℝ) := hh
      _≤(Z^BR0*Z^B)*Z^(commonExponent Lorig (N:ℝ) Lslot) :=
        mul_le_mul (mul_le_mul hR hprod2
          (Finset.prod_nonneg (fun i _=>mul_nonneg (by norm_num) (zero_le_one.trans (s.hP i))))
          (Real.rpow_nonneg hz.le _)) hGnorm (Nat.cast_nonneg _)
          (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _))
      _=Z^BRlive := by
        rw [←Real.rpow_add hz,←Real.rpow_add hz]
        rfl
  have hseedG : seed∣G := by
    have hh:=fixed_label_seed s ha cover u L J x seed hseed p
    rcases hG with rfl|rfl
    · exact hh.1
    · exact hh.2
  have hcanr := residual_canonical M Hray hHray Wslot Cap Lcap Z η₀ θ w σ freq t₀ R₀
    s hcanonical ha cover u L J x
  have hcanlive := allocated_canonical M Hray hHray Wslot Cap Lcap Z η₀
    (fun j : RestIndex q=>θ j.val.val) (fun j=>w j.val.val)
    (fun j=>σ j.val.val) (fun j=>freq j.val.val) t₀ (fun j=>R₀ j.val.val)
    r hcanr (zero_le_one.trans hb) cover G Balloc
  have hqP (i : ι) : 0<q.P i := zero_lt_one.trans_le (s.hP i)
  have hvolume : 1≤MixedSelectedVolume.volume q :=
    Finset.one_le_prod₀ (fun j _=>s.hP j.val.val)
  have hselectedP : MixedSelectedVolume.volume q≤∏i,s.P i :=
    injected_prod_le (fun j : q.J=>j.val.val)
      (fun i j he=>Subtype.ext (Subtype.ext he)) s.P s.hP
  have hscale : MixedSelectedVolume.scale q≤Z^B := by
    calc
      _≤(2:ℝ)^N*(∏i,s.P i) :=
        mul_le_mul (MixedSelectedVolume.padding_le q N hcard) hselectedP
          (zero_le_one.trans hvolume) (by positivity)
      _≤Z*Z^((N:ℝ)*Lslot) := mul_le_mul h2N hproduct
        (Finset.prod_nonneg (fun i _=>zero_le_one.trans (s.hP i))) hz.le
      _=Z^((N:ℝ)*Lslot+1) := by rw [Real.rpow_add hz,Real.rpow_one];ring
      _≤Z^B := Real.rpow_le_rpow_of_exponent_le hZ.le hslots
  have hscale1 : 1≤MixedSelectedVolume.scale q :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hvolume
  have hscaleInv : (MixedSelectedVolume.scale q)⁻¹≤Z^B :=
    (inv_le_one_of_one_le₀ hscale1).trans (Real.one_le_rpow hZ.le hB0)
  have hK:=padded_pos η Z Rdecl hz
  have hKcaps := hpaddedZ.2 η Rdecl B Bη hRdecl hRcap hη
  have hKinv : (paddedRadius η Z Rdecl)⁻¹≤Z^B :=
    hKcaps.2.trans (Real.rpow_le_rpow_of_exponent_le hZ.le hηB)
  have hinwidth:=padded_input_width η Z Rdecl hZ
  have hTlive : live.T=s.T := rfl
  have hdlive : live.d=(s.d.1*Balloc.val (Sum.inr 0),s.d.2*Balloc.val (Sum.inr 1)) := rfl
  have hsource := hbaseZ.2 q (liveIndices Balloc.val)
  have he := hsource
    (fun i=>θ i.val.val.val) (fun i=>w i.val.val.val)
    (fun i=>σ i.val.val.val) (fun i=>freq i.val.val.val) t₀ tp V
    (fun i=>R₀ i.val.val.val)
    (fun i=>hw i.val.val.val) (fun i=>hwL i.val.val.val)
    (fun i=>hσ i.val.val.val) (fun i=>hσhi i.val.val.val) hV
    (fun i=>hfreq i.val.val.val) (fun i=>hR₀ i.val.val.val)
    live hcanlive rfl (fun i=>hMs i.val.val.val) hRlive hHholes hholes
    (fun i P hP=>hHR i.val.val.val P hP) hFhole hX₁ hX₂ hY₁ hY₂
    η hη (paddedRadius η Z Rdecl) hK hKcaps.1 hKinv χ₀ msecond hm hml hm2
    ι q hcard hqP (fun i I hI=>(s.hpn i I hI).2) (fun i I _=>s.hν i I)
    (fun i v=>(s.hWnorm i v).trans (hMs i)) hscale hscaleInv hvolume
    (by simpa only [hinwidth] using hRdecl)
    (by rw [hinwidth,hTlive,hdlive]; exact hmixed) hnative keep hkeep heligible D hD hDcap X θwin hX rows
  have hE : 0≤E := by
    have hheight : 0≤height t₀ V s.t₁ s.t₂ := by unfold height;positivity
    have hfixed:=fixedPresentationCost_pos
    have hwindow:=heightCost_pos tp θwin
    dsimp only [E]
    positivity
  have hepaid : Z^(budgetStep B Bseed ε rho)*
      seededGroupedWindowRows q live ha D η tp keep ballProfile (paddedRadius η Z Rdecl)
        Vwin X θwin rows≤E/(pairNorm live.d*(D.absNorm:ℝ)) := by
    dsimp only [E]
    rw [←padded_paid η Z Rdecl]
    exact he
  have he' : Z^(budgetStep B Bseed ε rho)*raw/sourceVolume live≤
      E/(pairNorm live.d*(D.absNorm:ℝ)) := by
    have hid : raw/sourceVolume live=
        seededGroupedWindowRows q live ha D η tp keep ballProfile (paddedRadius η Z Rdecl)
          Vwin X θwin rows :=
      actual_finite_window_eq s ha (zero_le_one.trans hb) cover u L J x seed G hu hseedG
        Balloc D η tp keep Z Rdecl hz Vwin X θwin rows hrows
    rw [mul_div_assoc,hid]
    exact hepaid
  have hraw : Z^(budgetStep B Bseed ε rho)*raw≤
      sourceVolume live*(E/(pairNorm live.d*(D.absNorm:ℝ))) := by
    calc
      _≤(E/(pairNorm live.d*(D.absNorm:ℝ)))*sourceVolume live :=
        (div_le_iff₀ (sourceVolume_pos live)).mp he'
      _=_ := mul_comm _ _
  have hcost : ‖cactual‖^2≤‖ccanonical‖^2 :=
    actual_frozen_cost s ha cover u G L J x Balloc
  have hD0 : 0<(D.absNorm:ℝ) := zero_lt_one.trans_le (ideal_norm_one_le hD.ne_zero)
  have hbudget : 0≤sourceVolume live*(E/(pairNorm live.d*(D.absNorm:ℝ))) :=
    mul_nonneg (sourceVolume_pos live).le
      (div_nonneg hE (mul_pos (pairNorm_pos live.hd.1 live.hd.2) hD0).le)
  calc
    _=‖normalization (r.X₁*r.X₂) r.P‖^2*‖cactual‖^2*
        (Z^(budgetStep B Bseed ε rho)*raw) := by ring
    _≤‖normalization (r.X₁*r.X₂) r.P‖^2*‖cactual‖^2*
        (sourceVolume live*(E/(pairNorm live.d*(D.absNorm:ℝ)))) :=
      mul_le_mul_of_nonneg_left hraw (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _≤‖normalization (r.X₁*r.X₂) r.P‖^2*‖ccanonical‖^2*
        (sourceVolume live*(E/(pairNorm live.d*(D.absNorm:ℝ)))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (sq_nonneg _)) hbudget
    _=_ := allocated_paid_normalization r (zero_le_one.trans hb) cover G Balloc ccanonical D E

end
end Candidate.FourthPower.OuterFreshAllocatedWindow
