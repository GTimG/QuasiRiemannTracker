import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.FiberPrimitives
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record12518109Gain.FiberExponent
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotPlainCount

/- Adapted raw moment contract and actual fiber assembly from PR63
Candidate/Target830/Marked/GenericCountAssembly.lean, Apache-2.0.
The new adaptive widths and homogeneous exponent are proved here. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open scoped Classical BigOperators
namespace OAI.SevenEighths.Record12518109GainAssembly
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
open Record12518109Gain
variable {Row Label Slot : Type*} [Fintype Label]

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

theorem slots_empty_of_width_sum_zero (slots : Finset Slot) (widths : Slot→ℝ)
    (hw : ∀s∈slots,0<widths s) (hzero : (∑s∈slots,widths s)=0) : slots=∅ := by
  by_contra hne
  have hpos := Finset.sum_pos hw (Finset.nonempty_iff_ne_empty.mpr hne)
  linarith

theorem fiber_count (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (χ : Row→Label→Character) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U a ε T allowance mesh binWidth ζ εm C height : ℝ)
    (i : ℕ) (hU : 1<U) (ha0 : 31/50≤2*a-1) (ha : 2*a-1≤3/4)
    (hε : 0≤ε) (hε1 : ε≤1/100) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hζ : 0<ζ) (hC : 0<C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0≤∑ s∈slots,widths s)
    (witness : ∀u,SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (∑s∈slots,widths s)) T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀u∈rows,(witness u).label=label)
    (hJ : ∀u∈rows,(witness u).left=J) (hK : ∀u∈rows,(witness u).right=K)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s)=g s)
    (hmom : RawFiberMoments rows slots χ Q widths U a ε
      (cutoff (2*a-1) (∑s∈slots,widths s)) (3/4) εm C height label J K) :
    (rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(rho (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-gain (2*a-1) (∑s∈slots,widths s) 1-
        2*weightedMean slots widths g*(∑s∈slots,widths s)+155*ε+mesh+εm+(2*a-1)*ζ) := by
  let δ := 2*a-1
  let p := weightedMean slots widths g/δ
  let S := ∑s∈slots,widths s
  let t := cutoff δ S
  let r := Real.logb U ((2 : ℝ)^J.val)
  let m := Real.logb U ((2 : ℝ)^K.val)
  let A := 192*(1+height)*C
  have hδ : 0<δ := by dsimp [δ]; linarith
  have hA : 0<A := by dsimp [A]; positivity
  obtain ⟨u0,hu0⟩ := hne
  have hg (v : Slot) (hv : v∈slots) : 0≤g v ∧ g v≤δ/2 := by
    rw [←hbins u0 hu0 v hv]
    exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by dsimp [δ] at hδ; linarith)
  have hbounds : 0≤weightedMean slots widths g ∧ weightedMean slots widths g≤δ/2 := by
    by_cases hLp : 0<∑s∈slots,widths s
    · exact weightedMean_bounds slots widths g δ (fun v hv=>(hw v hv).le) hLp hg
    · have hzero : (∑s∈slots,widths s)=0 := by linarith
      have hempty := slots_empty_of_width_sum_zero slots widths hw hzero
      subst slots
      simp only [weightedMean,Finset.sum_empty,zero_div]
      constructor <;> linarith
  obtain ⟨hq0,hq⟩ := hbounds
  have hp0 : 0≤p := div_nonneg hq0 hδ.le
  have hp : p≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hmean : δ*p=weightedMean slots widths g := by dsimp [p]; field_simp
  have hlength := HeckeDetectorSupportedWitness.fiber_lengths rows ⟨u0,hu0⟩ χ U a ε t
    T allowance i hU witness J K hJ hK
  change t-r-ε≤m ∧ r≤t+ε ∧ m≤1/2+75*ε ∧ t-1/2-76*ε≤r ∧ 0≤m at hlength
  have hmono {x y : ℝ} (hxy : x≤y) : A*U^x≤A*U^y :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hxy) hA.le
  have hδmesh : δ*mesh≤mesh := by dsimp [δ]; nlinarith
  have hI : (rows.card : ℝ)≤A*U^(max 1 ((1+5*r)/6)-δ*r+(154*ε+mesh+εm)) :=
    hmom.inverseUnmarked.trans (hmono (by dsimp [δ]; linarith))
  have hP0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count rows χ U a ε t T allowance i
    hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK εm C height
    hC.le hheight hfreq hmom.plainUnmarked
  have hmax : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith [hlength.2.2.1])
  have hP : (rows.card : ℝ)≤A*U^(1-2*δ*m+(154*ε+mesh+εm)) :=
    hP0.trans (hmono (by dsimp [m,δ] at *; linarith))
  have hIM (z : ℝ) (hz : 0≤z) (hzS : z≤S) (hc1 : r+2*z<1) (hc2 : 2*r+8*z<3) :
      (rows.card : ℝ)≤A*U^(1-δ*r-2*δ*p*z+(154*ε+mesh+εm)) := by
    by_cases hLp : 0<∑s∈slots,widths s
    swap
    · have hS0 : S=0 := by dsimp [S]; linarith
      have hz0 : z=0 := by linarith
      rw [hz0] at hc1 ⊢
      rw [max_eq_left (by linarith : (1+5*r)/6≤1)] at hI
      simpa only [mul_zero,sub_zero,add_zero] using hI
    have hh := Record12518109GainFiber.inverse_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth z εm C height hmesh hbin hw hwm hLp hz hzS hbins hC.le hheight hfreq
      hc1 hc2 hmom.inverseMarked
    have hc : 12*(1+height)*C≤A := by dsimp [A]; nlinarith
    exact (hh.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _))).trans
      (hmono (by rw [←hmean]; nlinarith))
  have hPM (z : ℝ) (hz : 0≤z) (hzS : z≤S) (hc : 2*m+(9/2)*z≤1) :
      (rows.card : ℝ)≤A*U^(1-2*δ*m-2*δ*p*z+(154*ε+mesh+εm)) := by
    by_cases hLp : 0<∑s∈slots,widths s
    swap
    · have hS0 : S=0 := by dsimp [S]; linarith
      have hz0 : z=0 := by linarith
      rw [hz0]
      simpa only [mul_zero,sub_zero] using hP
    have hcap : 2*m+6*(3/4)*z≤1 := by linarith
    have hh := Record12518109GainFiber.plain_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth z (3/4) εm C height hmesh hbin hw hwm hLp hz hzS hbins
      (by norm_num) hC.le hheight hfreq hcap hmom.plainMarked
    exact hh.trans (hmono (by rw [←hmean]; nlinarith))
  by_cases hB : 0 < (rows.card : ℝ)
  · have hBA : 0 < (rows.card : ℝ)/A := div_pos hB hA
    have hlog (e : ℝ) (he : (rows.card : ℝ) ≤ A*U^e) : Real.logb U ((rows.card : ℝ)/A) ≤ e := by
      apply (Real.logb_le_iff_le_rpow hU hBA).mpr
      apply (div_le_iff₀ hA).mpr
      simpa only [mul_comm] using he
    have hh := Record12518109Gain.fiber_exponent ha0 ha hp0 hp hL hε hε1 hζ
      (show t-ε≤r+m by linarith [hlength.1]) hlength.2.1
      (hlog _ hI) (hlog _ hP) (fun z hz hzS hc1 hc2=>hlog _ (hIM z hz hzS hc1 hc2))
      (fun z hz hzS hc=>hlog _ (hPM z hz hzS hc))
    have hexp : Real.logb U ((rows.card : ℝ)/A) ≤ rho δ+δ*S-gain δ S 1-
        2*weightedMean slots widths g*S+155*ε+mesh+εm+δ*ζ := by rw [←hmean]; linarith
    have hh' := (Real.logb_le_iff_le_rpow hU hBA).mp hexp
    have hh'' := (div_le_iff₀ hA).mp hh'
    exact hh''.trans_eq (mul_comm _ _)
  · exact (le_of_not_gt hB).trans (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _))

end OAI.SevenEighths.Record12518109GainAssembly
end
