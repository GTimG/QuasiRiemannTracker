/- Repeated marks: the same-zero HIGH fiber count with `copies` repeated marked slots and one
detector cutoff per amplitude class. Fork of Collet's `High.feedback_fiber_count`
(Record1252270103Source/High/ActualFiber.lean, Apache-2.0); the analytic inputs are unchanged.

* The inverse witness may use each marked slot `copies` times. The selection is Collet's
  `inverse_fiber_count` applied to the replicated slot set `slots ×ˢ univ`, whose prefix
  selection takes `copies` copies of the highest slots with a single overshoot. Its energy is
  the overlap adapter `overlapping_annular_inverse_marked_energy` (supplied by the caller).
* The detector cutoff is `cutoffP` of the fiber's amplitude class `p = weightedMean / δ`.
* The gain is the class gain `gainP`; since `gainK ≤ gainP`, the count holds with `gainK`. -/
import Submissions.hailey_collet_1252270103.Record1252270103Source.High.ActualFiber
import Submissions.runbo_li_arvi_face_8746074_20261026.Gain.Selection
import Submissions.runbo_li_arvi_face_8746074_20261026.Gain.FiberClass
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Source
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
open HeckeDetectorFiberPartition HeckeDetectorDyadicProfiles HeckeDetectorInverseFiberCount
open QRH.Record1252270103Source.High
variable {Row Label Slot : Type*} [Fintype Label]

/-- The amplitude class, clamped to `[0,1/2]` (the identity on actual fibers). -/
def clampClass (x : ℝ) : ℝ := max 0 (min (1/2) x)

theorem clampClass_mem (x : ℝ) : 0 ≤ clampClass x ∧ clampClass x ≤ 1/2 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clampClass_eq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1/2) : clampClass x = x := by
  rw [clampClass, min_eq_right h1, max_eq_right h0]

/-- The detector cutoff of the amplitude class of the bins `g`. -/
def classCutoff (slots : Finset Slot) (widths g : Slot → ℝ) (copies : ℕ) (δ B lam h : ℝ) : ℝ :=
  QRH.RepeatedMarks.cutoffP δ (clampClass (weightedMean slots widths g/δ)) copies B lam h
    (∑ s∈slots, widths s) 1

/-- Every class cutoff is an admissible detector cutoff. -/
theorem classCutoff_bounds (slots : Finset Slot) (widths g : Slot → ℝ) (copies : ℕ)
    {δ B lam h : ℝ} (hδ0 : 1/2 ≤ δ) (hδ1 : δ ≤ 3/4) (hB : 22/23 ≤ B) (hlam : 1 < lam)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hS : 0 ≤ ∑ s∈slots, widths s) :
    1 ≤ classCutoff slots widths g copies δ B lam h ∧
      classCutoff slots widths g copies δ B lam h ≤ 10/7 := by
  have hc := clampClass_mem (weightedMean slots widths g/δ)
  have hP : QRH.RepeatedMarks.ClassParams δ (clampClass (weightedMean slots widths g/δ)) lam :=
    ⟨hδ0, hδ1, hc.1, hc.2, hlam⟩
  have hb := QRH.RepeatedMarks.cutoffP_bounds (K:=copies) (S:=∑ s∈slots, widths s) (Q:=1) hP
    (by positivity) hB hh0 hh1 hS (by norm_num)
  simpa only [classCutoff, mul_one] using hb

/-- The repeated-mark gain, `copies` copies, normalized ambient exponent `Q`. -/
def gainRep (copies : ℕ) (ν B lam h S Q : ℝ) : ℝ := QRH.RepeatedMarks.gainK ν copies B lam h S Q

/-- Fiber moments with the inverse marked moment for the replicated slot set. -/
structure FiberMomentsK (rows : Finset Row) (slots : Finset Slot) (copies : ℕ)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ) (widths : Slot→ℝ)
    (U a ε tstar B lam h εm C height : ℝ) (label : Label)
    (J K : Fin (dyadicLength U)) : Prop where
  base : OrdinaryFiberMoments rows slots χ Q widths U a ε tstar B lam h εm C height label J K
  inverseRep : ∀ selected : Finset (Slot × Fin copies),
    selected ⊆ slots ×ˢ (Finset.univ : Finset (Fin copies)) →
    Real.logb U ((2 : ℝ)^J.val)+2*(∑ x∈selected,widths x.1)<1 →
    2*Real.logb U ((2 : ℝ)^J.val)+8*(∑ x∈selected,widths x.1)<3 →
    ∀ n : ℕ,n≤2 → ∀ σ∈Set.Icc (0 : ℝ) 1,∀ freq∈Set.Icc (-height) height,
    ∑ u∈rows,‖polynomial (χ u label) true
      ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
      (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*(∏ x∈selected,Q u x.1)‖^2≤C*U^(1+εm)

theorem sum_rep (slots : Finset Slot) (copies : ℕ) (f : Slot → ℝ) :
    (∑ x∈slots ×ˢ (Finset.univ : Finset (Fin copies)), f x.1) = copies*∑ s∈slots, f s := by
  rw [Finset.sum_product]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem weightedMean_rep (slots : Finset Slot) (copies : ℕ) (hc : 1 ≤ copies)
    (w g : Slot → ℝ) :
    weightedMean (slots ×ˢ (Finset.univ : Finset (Fin copies))) (fun x => w x.1) (fun x => g x.1) =
      weightedMean slots w g := by
  have hc' : (copies : ℝ) ≠ 0 := by exact_mod_cast (show copies ≠ 0 by omega)
  simp only [weightedMean]
  rw [sum_rep slots copies (fun s => w s*g s), sum_rep slots copies w]
  by_cases h0 : (∑ s∈slots, w s) = 0
  · rw [h0]; simp
  · field_simp

theorem feedback_fiber_count_K (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (copies : ℕ) (hcopies : 1 ≤ copies)
    (χ : Row→Label→Character) (Q : Row→Slot→ℂ)
    (widths g : Slot→ℝ) (U a ε T allowance mesh binWidth ζ εm C height B lam h : ℝ)
    (hB0 : 22/23≤B) (hB1 : B≤1) (hlam : 1<lam) (hh0 : 0≤h) (hh1 : h<1)
    (i : ℕ) (hU : 1<U) (ha0 : 1/2≤2*a-1) (ha : 2*a-1≤3/4)
    (hε : 0≤ε) (hε1 : ε≤1/100) (hmesh : 0≤mesh) (hbin : 0<binWidth)
    (hζ : 0<ζ) (hC : 0<C) (hheight : 0≤height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤height)
    (hw : ∀ s∈slots,0<widths s) (hwm : ∀ s∈slots,widths s≤mesh)
    (hL : 0≤∑ s∈slots,widths s)
    (witness : ∀u,SupportedWitness (χ u) U a ε
      (classCutoff slots widths g copies (2*a-1) B lam h) T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀u∈rows,(witness u).label=label)
    (hJ : ∀u∈rows,(witness u).left=J) (hK : ∀u∈rows,(witness u).right=K)
    (hbins : ∀u∈rows,∀s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth (Q u s)=g s)
    (hmom : FiberMomentsK rows slots copies χ Q widths U a ε
      (classCutoff slots widths g copies (2*a-1) B lam h) B lam h εm C height label J K) :
    (rows.card : ℝ) ≤ (192*(1+height)*C)*
      U^(rho (2*a-1)+(2*a-1)*(∑s∈slots,widths s)-
        gainRep copies (2*a-1) B lam h (∑s∈slots,widths s) 1-
        2*weightedMean slots widths g*(∑s∈slots,widths s)+155*ε+mesh+εm+(2*a-1)*ζ) := by
  let δ := 2*a-1
  let p := weightedMean slots widths g/δ
  let S := ∑s∈slots,widths s
  let t := classCutoff slots widths g copies δ B lam h
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
  have hI : (rows.card : ℝ)≤A*U^(max 1 ((1+5*r)/6)-δ*r+(154*ε+mesh+εm)) :=
    hmom.base.inverseUnmarked.trans (hmono (by dsimp [δ]; linarith))
  have hP0 := HeckeDetectorNoSlotPlainCount.no_slot_plain_count rows χ U a ε t T allowance i
    hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK εm C height
    hC.le hheight hfreq hmom.base.plainUnmarked
  have hmax : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith [hlength.2.2.1])
  have hP : (rows.card : ℝ)≤A*U^(1-2*δ*m+(154*ε+mesh+εm)) :=
    hP0.trans (hmono (by dsimp [m,δ] at *; linarith))
  have hcopies' : (1:ℝ) ≤ copies := by exact_mod_cast hcopies
  -- the repeated-slot inverse count: Collet's selection on the replicated slots
  have hIM (z : ℝ) (hz : 0≤z) (hzS : z≤copies*S) (hc1 : r+2*z<1) (hc2 : 2*r+8*z<3) :
      (rows.card : ℝ)≤A*U^(1-δ*r-2*δ*p*z+(154*ε+mesh+εm)) := by
    by_cases hLp : 0<∑s∈slots,widths s
    swap
    · have hS0 : S=0 := by dsimp [S]; linarith
      have hz0 : z=0 := by rw [hS0, mul_zero] at hzS; linarith
      rw [hz0] at hc1 ⊢
      rw [max_eq_left (by linarith : (1+5*r)/6≤1)] at hI
      simpa only [mul_zero,sub_zero,add_zero] using hI
    let slotsR := slots ×ˢ (Finset.univ : Finset (Fin copies))
    have hLR : 0<∑ x∈slotsR,widths x.1 := by
      rw [sum_rep slots copies widths]; positivity
    have hzR : z≤∑ x∈slotsR,widths x.1 := by rw [sum_rep slots copies widths]; exact hzS
    have hh := Record12518109GainFiber.inverse_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slotsR
      (fun u x=>Q u x.1) (fun x=>widths x.1) (fun x=>g x.1)
      mesh binWidth z εm C height hmesh hbin
      (fun x hx=>hw x.1 (Finset.mem_product.mp hx).1)
      (fun x hx=>hwm x.1 (Finset.mem_product.mp hx).1) hLR hz hzR
      (fun u hu x hx=>hbins u hu x.1 (Finset.mem_product.mp hx).1) hC.le hheight hfreq
      hc1 hc2 hmom.inverseRep
    rw [weightedMean_rep slots copies hcopies widths g] at hh
    have hc : 12*(1+height)*C≤A := by dsimp [A]; nlinarith
    exact (hh.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _))).trans
      (hmono (by rw [←hmean]; nlinarith))
  have hPM (z : ℝ) (hz : 0≤z) (hzS : z≤S) (hzh : z≤h) (hc : 2*m+lam*z≤B) :
      (rows.card : ℝ)≤A*U^(1-2*δ*m-2*δ*p*z+(154*ε+mesh+εm)) := by
    by_cases hLp : 0<∑s∈slots,widths s
    swap
    · have hS0 : S=0 := by dsimp [S]; linarith
      have hz0 : z=0 := by linarith
      rw [hz0]
      simpa only [mul_zero,sub_zero] using hP
    have hh := ordinary_plain_fiber_count rows ⟨u0,hu0⟩ χ U a ε t T allowance i
      hU (by linarith) (fun u=>(witness u).toWitness) label J K hlabel hJ hK slots Q widths g
      mesh binWidth z B lam h εm C height hmesh hbin hw hwm hLp hz hzS hbins
      (by linarith) hzh hC.le hheight hfreq hc hmom.base.plainMarked
    exact hh.trans (hmono (by rw [←hmean]; nlinarith))
  -- the class parameters
  have hP' : QRH.RepeatedMarks.ClassParams δ p lam := ⟨ha0, ha, hp0, hp, hlam⟩
  have hPP : QRH.RepeatedMarks.ParentParams δ copies B lam h :=
    ⟨by linarith, ha, by positivity, hB0, hB1, hlam, hh0, hh1.le⟩
  by_cases hB : 0 < (rows.card : ℝ)
  · have hBA : 0 < (rows.card : ℝ)/A := div_pos hB hA
    have hlog (e : ℝ) (he : (rows.card : ℝ) ≤ A*U^e) : Real.logb U ((rows.card : ℝ)/A) ≤ e := by
      apply (Real.logb_le_iff_le_rpow hU hBA).mpr
      apply (div_le_iff₀ hA).mpr
      simpa only [mul_comm] using he
    let x := QRH.RepeatedMarks.xiP δ p copies B lam h S 1
    have hxlo := QRH.RepeatedMarks.xiP_lower (K:=copies) (B:=B) (h:=h) (S:=S) (Q:=1) hP'
      (by positivity) hB0 hh0 hL (by norm_num)
    have hbase : 5/6 ≤ QRH.RepeatedMarks.baseXi δ := by
      rw [QRH.RepeatedMarks.baseXi, le_div_iff₀ (by simp only [QRH.RepeatedMarks.densityDenom]; linarith)]
      simp only [QRH.RepeatedMarks.densityDenom]; linarith
    have hx0 : 5/6≤x := by simpa only [mul_one] using hbase.trans (by simpa only [mul_one] using hxlo)
    have hxB : x≤B := by
      simpa only [mul_one] using QRH.RepeatedMarks.xiP_le_BQ (K:=copies) (h:=h) (S:=S) (Q:=1) hP'
        hB0 hB1 (by norm_num)
    have hclamp : clampClass (weightedMean slots widths g/δ) = p := clampClass_eq hp0 hp
    have ht : t = QRH.RepeatedMarks.cutoffP δ p copies B lam h S 1 := by
      show QRH.RepeatedMarks.cutoffP δ (clampClass (weightedMean slots widths g/δ)) copies B lam h
        (∑ s∈slots, widths s) 1 = _
      rw [hclamp]
    have hbal : 6*δ*x+(5-6*δ)*t=5 := by
      have hb := QRH.RepeatedMarks.cutoffP_balance (K:=copies) (B:=B) (h:=h) (S:=S) (Q:=1) hP'
      simp only [QRH.RepeatedMarks.w, mul_one] at hb
      rw [ht]
      exact hb
    have hcut : t = QRH.RepeatedMarks.invThr p copies x S 1 +
        QRH.RepeatedMarks.plainThr p B lam h x S 1/2 := by
      rw [ht]
      rfl
    have hh := QRH.RepeatedMarks.fiber_exponent_class (ν:=δ) (B:=B) (lam:=lam) (h:=h) (x:=x)
      (t:=t) (p:=p) (K:=copies) (S:=S) (r:=r) (m:=m) (E:=Real.logb U ((rows.card : ℝ)/A))
      (loss:=154*ε+mesh+εm) (eps:=ε) (zeta:=ζ) ha0 ha hlam hh0 hx0 hxB hB1 hbal hcut hp0 hp
      hcopies' hL hε hε1 hζ (by linarith [hlength.1]) hlength.2.1
      (hlog _ hI) (hlog _ hP) (fun z hz hzS hc1 hc2=>hlog _ (hIM z hz hzS hc1 hc2))
      (fun z hz hzS hzh hc=>hlog _ (hPM z hz hzS hzh hc))
    -- 1 - δ ξ_p = ρ + δ S - f_p - 2 δ p S, and G_K ≤ f_p
    have hid := QRH.RepeatedMarks.gainP_count_identity δ p copies B lam h S 1
    have hle := QRH.RepeatedMarks.gainK_le_gainP hPP hL (by norm_num : (0:ℝ) ≤ 1)
      (show p ∈ QRH.RepeatedMarks.classes from ⟨hp0, hp⟩)
    have hrho : rho δ = 1 - δ*QRH.RepeatedMarks.baseXi δ := by
      simp only [rho, QRH.Record1252270103Source.High.baseXi, QRH.Record1252270103Source.High.densityDenom,
        QRH.RepeatedMarks.baseXi, QRH.RepeatedMarks.densityDenom]
    have hexp : Real.logb U ((rows.card : ℝ)/A) ≤ rho δ+δ*S-gainRep copies δ B lam h S 1-
        2*weightedMean slots widths g*S+155*ε+mesh+εm+δ*ζ := by
      simp only [gainRep]
      rw [←hmean, hrho]
      simp only [mul_one] at hid
      nlinarith
    have hh' := (Real.logb_le_iff_le_rpow hU hBA).mp hexp
    have hh'' := (div_le_iff₀ hA).mp hh'
    exact hh''.trans_eq (mul_comm _ _)
  · exact (le_of_not_gt hB).trans (mul_nonneg hA.le (Real.rpow_nonneg (by linarith) _))

end
end QRH.RepeatedMarks.Source
