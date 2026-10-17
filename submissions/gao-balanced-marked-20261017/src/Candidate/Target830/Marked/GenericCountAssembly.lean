import Candidate.Cycle63.Marked.GenericFiberCount
import Candidate.Target830.Marked.VariableSupply
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotPlainCount

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open scoped Classical BigOperators

namespace OAI.SevenEighths.Marked830Assembly
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount

/-- Turn the four genuine power bounds into the variable-width detector
count. No logarithmic cardinality hypothesis is left to the caller. -/
theorem count_from_four_powers {B A U d p S r m loss eps : ℝ}
    (hA : 0 < A) (hU : 1 < U) (hd0 : 31/50 ≤ d) (hd : d ≤ 7/10)
    (hp0 : 0 ≤ p) (hp : p ≤ 1/2) (hS : 0 ≤ S)
    (heps : 0 ≤ eps)
    (hlength : Marked830.VariableSupply.cutoff d p (Marked830.VariableSupply.chosenWidth d S)-eps ≤ r+m)
    (hrcap : r ≤ Marked830.VariableSupply.cutoff d p (Marked830.VariableSupply.chosenWidth d S)+eps)
    (hI : B ≤ A*U^(max 1 ((1+5*r)/6)-d*r+loss))
    (hP : B ≤ A*U^(1-2*d*m+loss))
    (hIM : r ≤ Marked830.VariableSupply.inverseThreshold d → B ≤ A*U^(1-d*r-2*d*p*Marked830.VariableSupply.inverseWidth d S+loss))
    (hPM : m ≤ Marked830.VariableSupply.plainThreshold d → B ≤ A*U^(1-2*d*m-2*d*p*Marked830.VariableSupply.plainWidth d S+loss)) :
    B ≤ A*U^(Marked830.VariableSupply.count d p (Marked830.VariableSupply.chosenWidth d S)+loss+eps) := by
  by_cases hB : 0 < B
  · have hBA : 0 < B/A := div_pos hB hA
    have hlog (e : ℝ) (he : B ≤ A*U^e) : Real.logb U (B/A) ≤ e := by
      apply (Real.logb_le_iff_le_rpow hU hBA).mpr
      apply (div_le_iff₀ hA).mpr
      simpa only [mul_comm] using he
    have hh := Marked830.VariableSupply.fiber_exponent hd0 hd hp0 hp hS heps hlength hrcap
      (hlog _ hI) (hlog _ hP) (fun hr => hlog _ (hIM hr)) (fun hm => hlog _ (hPM hm))
    have hh' := (Real.logb_le_iff_le_rpow hU hBA).mp hh
    have hh'' := (div_le_iff₀ hA).mp hh'
    simpa only [mul_comm] using hh''
  · exact (le_of_not_gt hB).trans (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _))

variable {Row Label Slot : Type*} [Fintype Label]

def binMean (slots : Finset Slot) (widths : Slot → ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  weightedMean slots widths (binValue slots ((2*a-1)/2) binWidth bin)

def binCutoff (slots : Finset Slot) (widths : Slot → ℝ) (a binWidth : ℝ)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) : ℝ :=
  Marked830.VariableSupply.cutoff (2*a-1) (binMean slots widths a binWidth bin/(2*a-1))
    (Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈slots,widths s))

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



/-- The three raw source moment gates and the already established unmarked
inverse detector gate, stated for a single actual row fiber. -/
structure RawFiberMoments (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε tstar κplain εm C height : ℝ) (label : Label)
    (J K : Fin (dyadicLength U)) : Prop where
  inverseUnmarked : (rows.card : ℝ) ≤ (192*(1+height)*C)*
    U^(max 1 ((1+5*Real.logb U ((2 : ℝ)^J.val))/6)-
      (2*a-1)*Real.logb U ((2 : ℝ)^J.val)+2*ε+εm)
  plainUnmarked : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Set.Icc (0 : ℝ) 1,
    ∀ freq∈Set.Icc (-height) height,
    ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
      polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq‖^2≤
        C*U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))+εm)
  inverseMarked : ∀ selected : Finset Slot,selected⊆slots →
    Real.logb U ((2 : ℝ)^J.val)+2*(∑ s∈selected,widths s)<1 →
    2*Real.logb U ((2 : ℝ)^J.val)+8*(∑ s∈selected,widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ σ∈Set.Icc (0 : ℝ) 1,∀ freq∈Set.Icc (-height) height,
    ∑ u∈rows,‖polynomial (χ u label) true
      ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
      (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*(∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)
  plainMarked : ∀ selected : Finset Slot,selected⊆slots →
    2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*(∑ s∈selected,widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ σ∈Set.Icc (0 : ℝ) 1,∀ freq∈Set.Icc (-height) height,
    ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
      polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
      (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*(∏ s∈selected,Q u s)‖^2≤C*U^(1+εm)

/-- Actual detector count for every positive slot supply. The inverse and
plain inequalities select independent widths at their strict density-dependent
caps; their exact 2:1 balance supplies the common detector cutoff. -/
theorem fiber_count (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (χ : Row→Label→Character) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U a ε T allowance mesh binWidth Δ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤7/10)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hΔ0 : 0≤Δ) (hΔ : Δ=0) (hC : 0<C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0<∑ s∈slots,widths s)
    (witness : ∀u,SupportedWitness (χ u) U a ε
      (Marked830.VariableSupply.cutoff (2*a-1) (weightedMean slots widths g/(2*a-1))
        (Marked830.VariableSupply.chosenWidth (2*a-1) (∑ s∈slots,widths s))) T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀u∈rows,(witness u).label=label)
    (hJ : ∀u∈rows,(witness u).left=J) (hK : ∀u∈rows,(witness u).right=K)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s)=g s)
    (hmom : RawFiberMoments rows slots χ Q widths U a ε
      (Marked830.VariableSupply.cutoff (2*a-1) (weightedMean slots widths g/(2*a-1))
        (Marked830.VariableSupply.chosenWidth (2*a-1) (∑ s∈slots,widths s))) (3/4+2*Δ) εm C height label J K) :
    (rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(Marked830.VariableSupply.count (2*a-1) (weightedMean slots widths g/(2*a-1))
        (Marked830.VariableSupply.chosenWidth (2*a-1) (∑ s∈slots,widths s))+155*ε+mesh+εm) := by
  let δ := 2*a-1
  let p := weightedMean slots widths g/δ
  let S := ∑s∈slots,widths s
  let s := Marked830.VariableSupply.chosenWidth δ S
  let si := Marked830.VariableSupply.inverseWidth δ S
  let sp := Marked830.VariableSupply.plainWidth δ S
  let t := Marked830.VariableSupply.cutoff δ p s
  let r := Real.logb U ((2 : ℝ)^J.val)
  let m := Real.logb U ((2 : ℝ)^K.val)
  let A := 192*(1+height)*C
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hA : 0<A := by dsimp [A]; positivity
  obtain ⟨u0,hu0⟩ := hne
  have hg (v : Slot) (hv : v∈slots) : 0≤g v ∧ g v≤δ/2 := by
    rw [←hbins u0 hu0 v hv]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by dsimp [δ] at hδ; linarith)
  obtain ⟨hq0,hq⟩ := weightedMean_bounds slots widths g δ (fun v hv=>(hw v hv).le) hL hg
  have hp0 : 0≤p := div_nonneg hq0 hδ.le
  have hp : p≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hmean : δ*p=weightedMean slots widths g := by dsimp [p]; field_simp
  obtain ⟨hi0,hiL,hi⟩ := Marked830.VariableSupply.inverseWidth_bounds ha0 ha hL.le
  obtain ⟨hpw0,hpL,hpw⟩ := Marked830.VariableSupply.plainWidth_bounds ha0 ha hL.le
  have hlength := HeckeDetectorSupportedWitness.fiber_lengths rows ⟨u0,hu0⟩ χ U a ε t
    T allowance i hU witness J K hJ hK
  change t-r-ε≤m ∧ r≤t+ε ∧ m≤1/2+75*ε ∧ t-1/2-76*ε≤r ∧ 0≤m at hlength
  have hmono {x y : ℝ} (hxy : x≤y) : A*U^x≤A*U^y :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hxy) hA.le
  have hδmesh : δ*mesh≤mesh := by nlinarith
  have hI : (rows.card : ℝ)≤A*U^(max 1 ((1+5*r)/6)-δ*r+(154*ε+mesh+εm)) :=
    hmom.inverseUnmarked.trans (hmono (by dsimp [δ]; linarith))
  have hP0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count rows χ U a ε t T allowance i
    hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK εm C height
    hC.le hheight hfreq hmom.plainUnmarked
  have hmax : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith [hlength.2.2.1])
  have hP : (rows.card : ℝ)≤A*U^(1-2*δ*m+(154*ε+mesh+εm)) :=
    hP0.trans (hmono (by dsimp [m,δ] at *; linarith))
  have hIM (hr : r≤Marked830.VariableSupply.inverseThreshold δ) :
      (rows.card : ℝ)≤A*U^(1-δ*r-2*δ*p*si+(154*ε+mesh+εm)) := by
    obtain ⟨hc1,hc2⟩ := Marked830.VariableSupply.inverse_capacities ha0 ha hr hi
    have hh := Cycle63MarkedFiber.inverse_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth si εm C height hmesh hbin hw hwm hL hi0 hiL hbins hC.le hheight hfreq
      hc1 hc2 hmom.inverseMarked
    have hc : 12*(1+height)*C≤A := by dsimp [A]; nlinarith
    calc
      _ ≤ (12*(1+height)*C)*U^(1-δ*r-2*weightedMean slots widths g*si+2*ε+δ*mesh+εm) := hh
      _ ≤ A*U^(1-δ*r-2*weightedMean slots widths g*si+2*ε+δ*mesh+εm) :=
        mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)
      _ ≤ _ := hmono (by rw [←hmean]; nlinarith)
  have hPM (hm : m≤Marked830.VariableSupply.plainThreshold δ) :
      (rows.card : ℝ)≤A*U^(1-2*δ*m-2*δ*p*sp+(154*ε+mesh+εm)) := by
    have hcap := Marked830.VariableSupply.plain_capacity hm hΔ0 hΔ hpw
    have hh := Cycle63MarkedFiber.plain_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth sp (3/4+2*Δ) εm C height hmesh hbin hw hwm hL hpw0 hpL hbins
      (by linarith) hC.le hheight hfreq hcap hmom.plainMarked
    exact hh.trans (hmono (by rw [←hmean]; nlinarith))
  have hh := count_from_four_powers hA hU ha0 ha hp0 hp hL.le hε
    (show t-ε≤r+m by linarith [hlength.1]) hlength.2.1 hI hP hIM hPM
  convert hh using 1 <;> dsimp [A,δ,p,s,S] <;> congr 2 <;> ring



/-- Jointly sum the actual slot product with the detector count. This is the
analytic gain over first discarding the amplitude and then paying its maximum. -/
theorem weighted_bound_of_card (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (Q : Row→Slot→ℂ) (widths g : Slot→ℝ)
    (U δ binWidth A loss : ℝ) (hU : 1<U) (hδ0 : 31/50≤δ) (hδ : δ≤7/10)
    (hbin : 0<binWidth) (hA : 0≤A) (hw : ∀s∈slots,0<widths s)
    (hL : 0<∑s∈slots,widths s)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) (δ/2) binWidth (Q u s)=g s)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^(δ/2+binWidth))
    (hcard : (rows.card : ℝ)≤A*
      U^(Marked830.VariableSupply.count δ (weightedMean slots widths g/δ)
        (Marked830.VariableSupply.chosenWidth δ (∑s∈slots,widths s))+loss)) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤ A*
      U^(Marked830.VariableSupply.density δ+δ*(∑s∈slots,widths s)-
        Marked830.VariableSupply.phi δ*Marked830.VariableSupply.chosenWidth δ (∑s∈slots,widths s)+loss+
        2*binWidth*(∑s∈slots,widths s)) := by
  let S := ∑s∈slots,widths s
  let p := weightedMean slots widths g/δ
  let s := Marked830.VariableSupply.chosenWidth δ S
  have hδpos : 0<δ := by linarith
  have hmean : δ*p=weightedMean slots widths g := by dsimp [p]; field_simp
  have hmeanS : weightedMean slots widths g*S=∑v∈slots,widths v*g v :=
    div_mul_cancel₀ _ hL.ne'
  obtain ⟨u0,hu0⟩ := hne
  have hg (v : Slot) (hv : v∈slots) : 0≤g v ∧ g v≤δ/2 := by
    rw [←hbins u0 hu0 v hv]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)
  have hp : p≤1/2 := (div_le_iff₀ hδpos).mpr
    (by linarith [(weightedMean_bounds slots widths g δ (fun v hv=>(hw v hv).le) hL hg).2])
  have hprod (u : Row) (hu : u∈rows) : ‖∏v∈slots,Q u v‖^2≤U^(2*δ*p*S+2*binWidth*S) := by
    have hh := HeckePrimeAmplitudeBins.product_upper slots widths (Q u) U (δ/2) binWidth
      hU hbin hw (hQ u hu)
    have hg' : (∑v∈slots,widths v*HeckePrimeAmplitudeBins.amplitude
        (U^(widths v)) (δ/2) binWidth (Q u v))=∑v∈slots,widths v*g v :=
      Finset.sum_congr rfl (fun v hv=>by rw [hbins u hu v hv])
    rw [hg',←hmeanS,←hmean] at hh
    have hh' := (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)).mpr hh
    convert hh' using 1
    rw [←Real.rpow_natCast,←Real.rpow_mul (by linarith : (0:ℝ)≤U)]
    congr 1
    ring
  have hjoint := Marked830.VariableSupply.joint_chosen_gap hδ0 hδ hp hL.le
  calc
    _ ≤ ∑u∈rows,U^(2*δ*p*S+2*binWidth*S) := Finset.sum_le_sum hprod
    _ = (rows.card : ℝ)*U^(2*δ*p*S+2*binWidth*S) := by simp
    _ ≤ (A*U^(Marked830.VariableSupply.count δ p s+loss))*U^(2*δ*p*S+2*binWidth*S) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by linarith) _)
    _ = A*U^((Marked830.VariableSupply.count δ p s+loss)+(2*δ*p*S+2*binWidth*S)) := by
      rw [mul_assoc,←Real.rpow_add (by linarith : 0<U)]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hU.le (by dsimp [s,S] at *; linarith)) hA



/-- The complete finite partition assembly, with an amplitude-adaptive detector
cutoff and explicit raw moment gates on each fiber. -/
theorem weighted_row_sum (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε T allowance mesh binWidth Δ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤7/10)
    (hε : 0≤ε) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hΔ0 : 0≤Δ) (hΔ : Δ=0) (hC : 0<C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀s∈slots,0<widths s) (hwm : ∀s∈slots,widths s≤mesh)
    (hL : 0<∑s∈slots,widths s)
    (witness : ∀bin : BinLabel slots ((2*a-1)/2) binWidth,
      ∀u,SupportedWitness (χ u) U a ε (binCutoff slots widths a binWidth bin) T allowance i)
    (hQ : ∀u∈rows,∀s∈slots,‖Q u s‖≤(U^(widths s))^((2*a-1)/2+binWidth))
    (hmom : ∀bin j J K,RawFiberMoments
      (adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K)
      slots χ Q widths U a ε (binCutoff slots widths a binWidth bin)
        (3/4+2*Δ) εm C height j J K) :
    (∑u∈rows,‖∏s∈slots,Q u s‖^2) ≤
      ((Fintype.card (BinLabel slots ((2*a-1)/2) binWidth) : ℝ)*
        Fintype.card Label*(dyadicLength U : ℝ)^2*(192*(1+height)*C))*
      U^(Marked830.VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-
        Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈slots,widths s)+
        155*ε+mesh+εm+2*binWidth*(∑s∈slots,widths s)) := by
  let A := 192*(1+height)*C
  let E := Marked830.VariableSupply.density (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-
    Marked830.VariableSupply.phi (2*a-1)*Marked830.VariableSupply.chosenWidth (2*a-1) (∑s∈slots,widths s)+
    155*ε+mesh+εm+2*binWidth*(∑s∈slots,widths s)
  have hA : 0≤A := by dsimp [A]; positivity
  have hf (bin : BinLabel slots ((2*a-1)/2) binWidth) (j : Label)
      (J K : Fin (dyadicLength U)) :
      (∑u∈adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K,
        ‖∏s∈slots,Q u s‖^2)≤A*U^E := by
    let F := adaptiveFiber rows slots widths Q χ U a ε T allowance binWidth i hbin witness bin j J K
    by_cases hne : F.Nonempty
    · have hfields (u : Row) (hu : u∈F) := adaptiveFiber_fields rows slots widths Q χ U a ε
        T allowance binWidth i hbin witness bin j J K u hu
      have hc := fiber_count F hne slots χ Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U a ε T allowance mesh binWidth Δ εm C height
        i hU ha0 ha hε hmesh hbin hΔ0 hΔ hC hheight hfreq hw hwm hL
        (witness bin) j J K (fun u hu=>(hfields u hu).2.1)
        (fun u hu=>(hfields u hu).2.2.1) (fun u hu=>(hfields u hu).2.2.2.1)
        (fun u hu=>(hfields u hu).2.2.2.2) (hmom bin j J K)
      have hh := weighted_bound_of_card F hne slots Q widths
        (binValue slots ((2*a-1)/2) binWidth bin) U (2*a-1) binWidth A
        (155*ε+mesh+εm) hU ha0 ha hbin hA hw hL
        (fun u hu=>(hfields u hu).2.2.2.2)
        (fun u hu=>hQ u (hfields u hu).1) (by simpa only [A,add_assoc] using hc)
      convert hh using 1 <;> dsimp [E] <;> congr 2 <;> ring
    · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (∑u∈F,‖∏s∈slots,Q u s‖^2)≤A*U^E
      rw [he,Finset.sum_empty]
      exact mul_nonneg hA (Real.rpow_nonneg (by linarith) _)
  rw [adaptive_fiber_sum rows slots widths Q χ U a ε T allowance binWidth i hbin witness]
  calc
    _ ≤ ∑(_bin : BinLabel slots ((2*a-1)/2) binWidth),∑(_j : Label),
        ∑(_J : Fin (dyadicLength U)),∑(_K : Fin (dyadicLength U)),A*U^E :=
      Finset.sum_le_sum (fun bin _=>Finset.sum_le_sum (fun j _=>
        Finset.sum_le_sum (fun J _=>Finset.sum_le_sum (fun K _=>hf bin j J K))))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end OAI.SevenEighths.Marked830Assembly
#print axioms OAI.SevenEighths.Marked830Assembly.fiber_count
#print axioms OAI.SevenEighths.Marked830Assembly.weighted_row_sum

namespace OAI.SevenEighths.Marked830Assembly
open HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition

/-- The finite label set contains one rounded endpoint beyond the amplitude
cap; this explicit bound also covers bins not realized by any row. -/
theorem label_bounds {cap bw x : ℝ} (hcap : 0≤cap) (hbw : 0<bw)
    (hx : x∈HeckePrimeAmplitudeBins.labels cap bw) : 0≤x ∧ x≤cap+bw := by
  simp only [HeckePrimeAmplitudeBins.labels,Finset.mem_insert,Finset.mem_image,
    Finset.mem_Icc] at hx
  rcases hx with rfl | rfl | ⟨n,⟨hn0,hn⟩,rfl⟩
  · constructor <;> linarith
  · constructor <;> linarith
  · have hn0' : (0:ℝ)≤n := by exact_mod_cast hn0
    have hn' : (n:ℝ)≤⌈cap/bw⌉ := by exact_mod_cast hn
    have hceil : (⌈cap/bw⌉ : ℝ)<cap/bw+1 := Int.ceil_lt_add_one _
    have hquot : cap/bw*bw=cap := div_mul_cancel₀ _ hbw.ne'
    constructor
    · positivity
    · nlinarith [mul_lt_mul_of_pos_right (hn'.trans_lt hceil) hbw]

/-- All bins, including unused rounded endpoint bins, have a legal detector
cutoff. Therefore the actual supported witness theorem supplies the entire
adaptive witness family before the row partition is formed. -/
theorem binCutoff_bounds {Slot : Type*} (slots : Finset Slot) (widths : Slot→ℝ)
    (a binWidth : ℝ) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤7/10)
    (hbin : 0<binWidth) (hbin' : binWidth≤(2*a-1)/2)
    (hw : ∀s∈slots,0≤widths s) (hL : 0<∑s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) :
    1≤binCutoff slots widths a binWidth bin ∧ binCutoff slots widths a binWidth bin≤3/2 := by
  let δ := 2*a-1
  let g := binValue slots (δ/2) binWidth bin
  let p := weightedMean slots widths g/δ
  let s := Marked830.VariableSupply.chosenWidth δ (∑v∈slots,widths v)
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hg (v : Slot) (hv : v∈slots) : 0≤g v ∧ g v≤(2*δ)/2 := by
    have hh := label_bounds (show 0≤δ/2 by positivity) hbin (bin ⟨v,hv⟩).property
    dsimp [g,binValue]
    rw [dif_pos hv]
    constructor
    · exact hh.1
    · dsimp [δ] at *; linarith
  obtain ⟨hq0,hq⟩ := weightedMean_bounds slots widths g (2*δ) hw hL hg
  have hp0 : 0≤p := div_nonneg hq0 hδ.le
  have hp : p≤1 := (div_le_iff₀ hδ).mpr (by linarith)
  obtain ⟨hs0,hsL,hs⟩ := Marked830.VariableSupply.chosenWidth_bounds ha0 ha hL.le
  have hps0 : 0≤p*s := mul_nonneg hp0 hs0
  have hps : p*s≤11/114 := by nlinarith [mul_nonneg (sub_nonneg.mpr hp) hs0]
  have hden : 0<5-2*δ := by dsimp [δ]; linarith
  change 1≤Marked830.VariableSupply.cutoff δ p s ∧ Marked830.VariableSupply.cutoff δ p s≤3/2
  unfold Marked830.VariableSupply.cutoff
  constructor
  · apply (le_div_iff₀ hden).mpr
    nlinarith [mul_le_mul_of_nonneg_left hps hδ.le]
  · apply (div_le_iff₀ hden).mpr
    have hz : 0≤δ*(p*s) := mul_nonneg hδ.le hps0
    dsimp [δ] at *
    nlinarith

end OAI.SevenEighths.Marked830Assembly
#print axioms OAI.SevenEighths.Marked830Assembly.binCutoff_bounds
