import Candidate.Cycle63.Marked.GenericFiberCount
import Candidate.Target830.Marked.GenericCountAssembly
import Candidate.Uneven.BootstrapPowers
import Candidate.Uneven.AuxiliarySchedule
import Candidate.Uneven.SaturatedScalar

/- Original module: Candidate.Uneven.BootstrapPlainFiber. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
open Set
namespace OAI.SevenEighths.BootstrapAssembly
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorInverseFiberCount
open Cycle63MarkedFiber

theorem plain_fiber_count_at_selected_width {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 1/2≤ a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (mesh binWidth z εm C height : ℝ) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤ z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (Q u s)=g s)
    (hC : 0≤ C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      (∑ s∈selected,widths s)≤ z →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,Q u s)‖^2≤ C*U^(1+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(1-2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)-2*weightedMean slots widths g*z+
        4*ε+(2*a-1)*mesh+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_common_product rows hne slots
    Q widths g U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hUp : 0<U := zero_lt_one.trans hU
  have hDp : 0<U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤ C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,Q u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq (hraw selected hsub hlen)
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        (∏ s∈selected,Q u s)‖^2≤
      (192*(1+height)*C)*U^(1+εm) := by
    convert he using 1; ring
  have hc := HeckeDetectorRowCount.plain_count rows (fun u => χ u label)
    positiveAnnular (U^m) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,Q u s)
    U (2*a-1) m (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (192*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.2) hspike he'
  convert hc using 1; congr 2; ring


end OAI.SevenEighths.BootstrapAssembly
end

/- Original module: Candidate.Uneven.BootstrapFiber. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.BootstrapAssembly
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
open Marked830Assembly
variable {Row Label Slot : Type*} [Fintype Label]

def AuxiliaryPlainMoments (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U εm C height : ℝ) (label : Label) (K : Fin (dyadicLength U)) : Prop :=
    ∀ selected : Finset Slot,selected⊆slots →
      (∑s∈selected,widths s)∈Set.Icc Sil.Uneven.AuxiliarySource.widthLo Sil.Uneven.AuxiliarySource.widthHi →
      (81/200:ℝ) ≤ Real.logb U ((2:ℝ)^K.val) →
      Real.logb U ((2:ℝ)^K.val) ≤ 9/20 →
      2*Real.logb U ((2:ℝ)^K.val)+Sil.Uneven.Bootstrap.auxLambda*(∑s∈selected,widths s)
        ≤ Sil.Uneven.Bootstrap.auxB →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Set.Icc (0:ℝ) 1,∀ freq∈Set.Icc (-height) height,
      ∑u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2:ℝ)^K.val))) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2:ℝ)^K.val))) σ freq*(∏s∈selected,Q u s)‖^2 ≤ C*U^(1+εm)

theorem fiber_count (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (χ : Row→Label→Character) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U a ε T allowance mesh binWidth Δ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤33/50)
    (hε : 0<ε) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hΔ0 : 0≤ Δ) (hΔ : Δ=0) (hC : 0<C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s)
    (witness : ∀u,SupportedWitness (χ u) U a ε
      (Sil.Uneven.Bootstrap.cutoff (2*a-1) (∑s∈slots,widths s)) T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀u∈rows,(witness u).label=label)
    (hJ : ∀u∈rows,(witness u).left=J) (hK : ∀u∈rows,(witness u).right=K)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s)=g s)
    (hmom : RawFiberMoments rows slots χ Q widths U a ε
      (Sil.Uneven.Bootstrap.cutoff (2*a-1) (∑s∈slots,widths s)) (3/4+2*Δ) εm C height label J K)
    (hauxraw : AuxiliaryPlainMoments rows slots χ Q widths U εm C height label K) :
    (rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈slots,widths s)+
        (2*a-1)*(∑s∈slots,widths s)-2*weightedMean slots widths g*(∑s∈slots,widths s)+401*ε+mesh+εm) := by
  let δ := 2*a-1
  let p := weightedMean slots widths g/δ
  let S := ∑s∈slots,widths s
  let t := Sil.Uneven.Bootstrap.cutoff δ S
  let r := Real.logb U ((2 : ℝ)^J.val)
  let m := Real.logb U ((2 : ℝ)^K.val)
  let A := 192*(1+height)*C
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hA : 0<A := by dsimp [A]; positivity
  obtain ⟨u0,hu0⟩ := hne
  have hg (v : Slot) (hv : v∈slots) : 0≤ g v ∧ g v≤ δ/2 := by
    rw [←hbins u0 hu0 v hv]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by dsimp [δ] at hδ; linarith)
  obtain ⟨hq0,hq⟩ := weightedMean_bounds slots widths g δ (fun v hv=>(hw v hv).le) hL hg
  have hp0 : 0≤ p := div_nonneg hq0 hδ.le
  have hp : p≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hmean : δ*p=weightedMean slots widths g := by dsimp [p]; field_simp
  have hcut := Sil.Uneven.Bootstrap.cutoff_bounds
    (d:=δ) (S:=S) ha0 ha hL.le
  change 1≤ t ∧ t≤3/2 at hcut
  have hlength := HeckeDetectorSupportedWitness.fiber_lengths rows ⟨u0,hu0⟩ χ U a ε t
    T allowance i hU witness J K hJ hK
  change t-r-ε≤ m ∧ r≤ t+ε ∧ m≤1/2+75*ε ∧ t-1/2-76*ε≤ r ∧ 0≤ m at hlength
  have hmono {x y : ℝ} (hxy : x≤ y) : A*U^x≤ A*U^y :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hxy) hA.le
  have hδmesh : δ*mesh≤ mesh := by nlinarith
  have hI : (rows.card : ℝ)≤ A*U^(max 1 ((1+5*r)/6)-δ*r+(400*ε+mesh+εm)) :=
    hmom.inverseUnmarked.trans (hmono (by dsimp [δ]; linarith))
  have hP0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count rows χ U a ε t T allowance i
    hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK εm C height
    hC.le hheight hfreq hmom.plainUnmarked
  have hmax : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith [hlength.2.2.1])
  have hP : (rows.card : ℝ)≤ A*U^(1-2*δ*m+(400*ε+mesh+εm)) :=
    hP0.trans (hmono (by dsimp [m,δ] at *; linarith))
  have hIM (hr : r<1) :
      (rows.card : ℝ)≤ A*U^(1-δ*r-2*δ*p*min S ((1-r)/2)+(400*ε+mesh+εm)) := by
    let si := max 0 (min S ((1-r)/2)-100*ε)
    have hrlo : 1/2-76*ε≤ r := by linarith [hlength.2.2.2.1,hcut.1]
    obtain ⟨hi0,hiL,hloss,hc1,hc2⟩ :=
      Sil.Uneven.Saturated.inverse_width_gates hL.le hε hrlo hr
    have hh := Cycle63MarkedFiber.inverse_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth si εm C height hmesh hbin hw hwm hL hi0 hiL hbins hC.le hheight hfreq
      hc1 hc2 hmom.inverseMarked
    have hc : 12*(1+height)*C≤ A := by dsimp [A];nlinarith
    have hmean0 : 0≤2*δ*p := by positivity
    have hmean1 : 2*δ*p≤1 := by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hp)]
    have hprod := mul_le_mul_of_nonneg_left hloss hmean0
    have hfee := mul_le_mul_of_nonneg_right hmean1 (show 0≤100*ε by positivity)
    have hpay : 2*δ*p*(min S ((1-r)/2)-si)≤100*ε := by
      dsimp only [si]
      nlinarith only [hprod,hfee]
    calc
      _ ≤ (12*(1+height)*C)*U^(1-δ*r-2*weightedMean slots widths g*si+2*ε+δ*mesh+εm) := hh
      _ ≤ A*U^(1-δ*r-2*weightedMean slots widths g*si+2*ε+δ*mesh+εm) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := hmono (by rw [←hmean];nlinarith only [hpay,hδmesh,hε])
  have hPM (hm : m≤1/2) :
      (rows.card : ℝ)≤ A*U^(1-2*δ*m-2*δ*p*min S (2*(1-2*m)/9)+(400*ε+mesh+εm)) := by
    let sp := min S (2*(1-2*m)/9)
    have hpw0 : 0≤ sp := le_min hL.le (by linarith)
    have hpL : sp≤ S := min_le_left _ _
    have hcap : 2*m+6*(3/4+2*Δ)*sp≤1 := by
      rw [hΔ]
      have hb : sp≤2*(1-2*m)/9 := min_le_right _ _
      linarith
    have hh := Cycle63MarkedFiber.plain_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth sp (3/4+2*Δ) εm C height hmesh hbin hw hwm hL hpw0 hpL hbins
      (by linarith) hC.le hheight hfreq hcap hmom.plainMarked
    exact hh.trans (hmono (by rw [←hmean];nlinarith))
  have hAux (hS : Sil.Uneven.Bootstrap.auxLower ≤ S)
      (hm0 : 81/200 ≤ m) (hm1 : m ≤ Sil.Uneven.Bootstrap.auxCutoff) :
      (rows.card:ℝ) ≤ A*U^(1-2*δ*m-2*δ*p*min S
        (min Sil.Uneven.Bootstrap.auxUpper ((Sil.Uneven.Bootstrap.auxB-2*m)/Sil.Uneven.Bootstrap.auxLambda))+
        (400*ε+mesh+εm)) := by
    let z := min S (min Sil.Uneven.Bootstrap.auxUpper
      ((Sil.Uneven.Bootstrap.auxB-2*m)/Sil.Uneven.Bootstrap.auxLambda))
    have hmhi : m ≤ 9/20 := hm1.trans Sil.Uneven.Bootstrap.aux_length_gates.2.1.le
    have hlambda : 0 < Sil.Uneven.Bootstrap.auxLambda := by norm_num [Sil.Uneven.Bootstrap.auxLambda]
    have hnum : 0 ≤ Sil.Uneven.Bootstrap.auxB-2*m := by
      norm_num [Sil.Uneven.Bootstrap.auxB] at *
      linarith only [hmhi]
    have hz0 : 0 ≤ z := le_min hL.le (le_min
      (by norm_num [Sil.Uneven.Bootstrap.auxUpper]) (div_nonneg hnum hlambda.le))
    have hzS : z ≤ S := min_le_left _ _
    have hh := plain_fiber_count_at_selected_width rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth z εm C height hmesh hbin hw hwm hL hz0 hzS hbins hC.le hheight hfreq
      (by
        intro selected hsub hwidth
        have hnonneg : 0 ≤ ∑s∈selected,widths s :=
          Finset.sum_nonneg (fun s hs=>(hw s (hsub hs)).le)
        have hcap : (∑s∈selected,widths s) ≤ min (7/250)
            ((Sil.Uneven.AuxiliarySource.B-2*m)/Sil.Uneven.AuxiliarySource.lambda) :=
          hwidth.trans (min_le_right _ _)
        rcases Sil.Uneven.AuxiliarySource.selected_width_gate hm1 hnonneg hcap with hold|hnew
        · apply hmom.plainMarked selected hsub
          rw [hΔ]
          change 2*m+6*(3/4+2*0)*(∑s∈selected,widths s) ≤ 1
          linarith only [hold]
        · exact hauxraw selected hsub hnew.1 hm0 hmhi hnew.2)
    exact hh.trans (hmono (by rw [←hmean];nlinarith only [hδmesh,hε]))
  have hh := Sil.Uneven.Bootstrap.count_from_powers hA hU ha0 ha hp0 hp hL.le hε.le
    (show t-ε≤ r+m by linarith [hlength.1]) hlength.2.1 hI hP hIM hPM hAux
  have he : 2*δ*p*S=2*weightedMean slots widths g*S := by rw [←hmean];ring
  rw [he] at hh
  convert hh using 1 <;> dsimp [A,δ,S] <;> congr 2 <;> ring

end OAI.SevenEighths.BootstrapAssembly
end

/- Original module: Candidate.Uneven.BootstrapAssembly. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.BootstrapAssembly
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
open Marked830Assembly (RawFiberMoments)
variable {Row Label Slot : Type*} [Fintype Label]

def binMean (slots : Finset Slot) (widths : Slot → ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)

def binCutoff (slots : Finset Slot) (widths : Slot → ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  Sil.Uneven.Bootstrap.cutoff (2*a-1) (∑s∈slots,widths s)

def adaptiveKey (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (u : Row) : BinLabel slots ((2*a-1)/2) binWidth × Label ×
        Fin (dyadicLength U) × Fin (dyadicLength U) :=
  let b := amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u
  (b,(witness b u).label,(witness b u).left,(witness b u).right)

def adaptiveFiber (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => adaptiveKey slots widths Q χ U a ε T allowance binWidth i hbin witness u =
    (bin,j,J,K))

theorem adaptiveFiber_fields
    (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
    (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u ∈ adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K) :
    u ∈ rows ∧ (witness bin u).label=j ∧ (witness bin u).left=J ∧
      (witness bin u).right=K ∧ ∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s) =
        binValue slots ((2*a-1)/2) binWidth bin s := by
  obtain ⟨hrow,hkey⟩ := Finset.mem_filter.mp hu
  have hb : amplitudeLabel slots U ((2*a-1)/2) binWidth hbin widths Q u = bin :=
    congrArg Prod.fst hkey
  have hw : (witness bin u).label=j ∧ (witness bin u).left=J ∧ (witness bin u).right=K := by
    dsimp [adaptiveKey] at hkey
    rw [hb] at hkey
    simpa only [Prod.mk.injEq,true_and] using hkey
  refine ⟨hrow,hw.1,hw.2.1,hw.2.2,?_⟩
  intro s hs
  have hv := congrArg (fun b : BinLabel slots ((2*a-1)/2) binWidth => (b ⟨s,hs⟩).val) hb
  simpa only [amplitudeLabel,binValue,dite_eq_left hs] using hv

theorem adaptive_fiber_sum (rows : Finset Row) (slots : Finset Slot) (widths : Slot → ℝ)
    (Q : Row → Slot → ℂ) (χ : Row → Label → Character)
    (U a ε T allowance binWidth : ℝ) (i : ℕ) (hbin : 0 < binWidth)
    (witness : ∀ bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (f : Row → ℝ) :
    (∑u∈rows,f u) = ∑bin,∑j,∑J,∑K,
      ∑u∈adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K,f u := by
  have hh := Finset.sum_fiberwise_of_maps_to (s:=rows) (t:=Finset.univ)
    (g:=adaptiveKey slots widths Q χ U a ε T allowance binWidth i hbin witness)
    (f:=f) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,adaptiveFiber] using hh.symm



theorem weighted_bound_of_card (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (U δ binWidth A loss : ℝ) (hU : 1<U) (hδ0 : 31/50≤ δ) (hδ : δ≤33/50)
    (hbin : 0<binWidth) (hA : 0≤ A) (hw : ∀s∈slots,0<widths s)
    (hL : 0<∑s∈slots,widths s)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (δ/2) binWidth (Q u s)=g s)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^(δ/2+binWidth))
    (hcard : (rows.card : ℝ)≤ A*U^(Sil.Uneven.Bootstrap.count δ (∑s∈slots,widths s)+
      δ*(∑s∈slots,widths s)-2*weightedMean slots widths g*(∑s∈slots,widths s)+loss)) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤ A*
      U^(Sil.Uneven.Bootstrap.count δ (∑s∈slots,widths s)+δ*(∑s∈slots,widths s)+loss+
        2*binWidth*(∑s∈slots,widths s)) := by
  let S := ∑s∈slots,widths s
  let mean := weightedMean slots widths g
  have hmeanS : mean*S=∑v∈slots,widths v*g v := div_mul_cancel₀ _ hL.ne'
  have hprod (u : Row) (hu : u∈rows) : ‖∏v∈slots,Q u v‖^2≤ U^(2*mean*S+2*binWidth*S) := by
    have hh := HeckePrimeAmplitudeBins.product_upper slots widths (Q u) U (δ/2) binWidth
      hU hbin hw (hQ u hu)
    have hg' : (∑v∈slots,widths v*HeckePrimeAmplitudeBins.amplitude
        (U^(widths v)) (δ/2) binWidth (Q u v))=∑v∈slots,widths v*g v :=
      Finset.sum_congr rfl (fun v hv=>by rw [hbins u hu v hv])
    rw [hg',←hmeanS] at hh
    have hh' := (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)).mpr hh
    convert hh' using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : (0:ℝ)≤ U)]
    congr 1
    ring
  calc
    _ ≤ ∑u∈rows,U^(2*mean*S+2*binWidth*S) := Finset.sum_le_sum hprod
    _ = (rows.card : ℝ)*U^(2*mean*S+2*binWidth*S) := by simp
    _ ≤ (A*U^(Sil.Uneven.Bootstrap.count δ S+δ*S-2*mean*S+loss))*U^(2*mean*S+2*binWidth*S) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by linarith) _)
    _ = _ := by
      rw [mul_assoc,←Real.rpow_add (by linarith : 0<U)]
      congr 1
      dsimp [S]
      ring

theorem weighted_row_sum (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth Δ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤33/50)
    (hε : 0<ε) (hmesh : 0≤ mesh) (hbin : 0<binWidth)
    (hΔ0 : 0≤ Δ) (hΔ : Δ=0) (hC : 0<C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤ mesh)
    (hL : 0<∑s∈slots,widths s)
    (witness : ∀bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀bin j J K,RawFiberMoments
      (adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K)
      slots χ Q widths U a ε (binCutoff slots widths a binWidth bin)
        (3/4+2*Δ) εm C height j J K)
    (hauxmom : ∀bin j J K,AuxiliaryPlainMoments
      (adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K)
      slots χ Q widths U εm C height j K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈slots,widths s)+(2*a-1)*(∑s∈slots,widths s)+
        401*ε+mesh+εm+2*binWidth*(∑s∈slots,widths s)) := by
  let A := 192*(1+height)*C
  let E := Sil.Uneven.Bootstrap.count (2*a-1) (∑s∈slots,widths s)+(2*a-1)*(∑s∈slots,widths s)+
    401*ε+mesh+εm+2*binWidth*(∑s∈slots,widths s)
  have hA : 0≤ A := by dsimp [A]; positivity
  have hf (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
      (J K : Fin (dyadicLength U)) :
      (∑u∈adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K,
        ‖∏s∈slots,Q u s‖^2)≤ A*U^E := by
    let F := adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K
    by_cases hne : F.Nonempty
    · have hfields (u : Row) (hu : u∈F) := adaptiveFiber_fields rows slots widths Q χ U a ε
        T allowance binWidth i hbin witness bin j J K u hu
      have hc := fiber_count F hne slots χ Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U a ε T allowance mesh binWidth Δ εm C height
        i hU ha0 ha hε hmesh hbin hΔ0 hΔ hC hheight hfreq hw hwm hL
        (witness bin) j J K (fun u hu=>(hfields u hu).2.1)
        (fun u hu=>(hfields u hu).2.2.1) (fun u hu=>(hfields u hu).2.2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.2) (hmom bin j J K) (hauxmom bin j J K)
      have hh := weighted_bound_of_card F hne slots Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U (2*a-1) binWidth A
        (401*ε+mesh+εm) hU ha0 ha hbin hA hw hL
        (fun u hu=>(hfields u hu).2.2.2.2)
        (fun u hu=>hQ u (hfields u hu).1) (by simpa only [A,add_assoc] using hc)
      convert hh using 1 <;> dsimp [E] <;> congr 2 <;> ring
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (∑u∈F,‖∏s∈slots,Q u s‖^2)≤ A*U^E
      rw [he,Finset.sum_empty]
      exact mul_nonneg hA (Real.rpow_nonneg (by linarith) _)
  rw [adaptive_fiber_sum rows slots widths Q χ U a ε T allowance binWidth i hbin witness]
  calc
    _ ≤ ∑(_bin : BinLabel slots ((2*a-1)/2) binWidth),∑(_j : Label),
        ∑(_J : Fin (dyadicLength U)),∑(_K : Fin (dyadicLength U)),A*U^E :=
      Finset.sum_le_sum (fun bin _=>Finset.sum_le_sum (fun j _=>
        Finset.sum_le_sum (fun J _=>Finset.sum_le_sum (fun K _=>hf bin j J K))))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

theorem binCutoff_bounds {Slot : Type*} (slots : Finset Slot) (widths : Slot→ℝ)
    (a binWidth : ℝ) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤33/50)
    (hbin : 0<binWidth) (hbin' : binWidth≤(2*a-1)/2)
    (hw : ∀s∈slots,0≤ widths s) (hL : 0<∑s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) :
    1≤ binCutoff slots widths a binWidth bin ∧ binCutoff slots widths a binWidth bin≤3/2 := by
  exact Sil.Uneven.Bootstrap.cutoff_bounds ha0 ha
    (Finset.sum_nonneg hw)

end OAI.SevenEighths.BootstrapAssembly
end
