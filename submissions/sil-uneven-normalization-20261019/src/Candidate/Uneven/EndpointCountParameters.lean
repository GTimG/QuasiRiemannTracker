import Candidate.Uneven.MainCountConcrete
import Candidate.Uneven.MainCountArithmetic
import Candidate.Target830.Physical.CountChoice
import Candidate.Uneven.MainCountFromMoments
import Candidate.Affine.Balanced
import Candidate.Uneven.EndpointData

/- Original module: Candidate.Uneven.MainCountOldWindows. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainCount
noncomputable section

def Window.ofOld (w : Target830.Count.Window) : Window where
  plane := Plane.ofOld w.plane
  deltaLo := w.deltaLo
  deltaHi := w.deltaHi
  pLo := w.pLo
  bounds := w.bounds

theorem Window.ofOld_admissible (w : Target830.Count.Window) {d p : ℝ}
    (h : Target830.Count.Admissible w.plane d p) :
    Admissible (Window.ofOld w).plane d p := by
  constructor
  · simpa only [Window.ofOld,guardD,Target830.Count.guardD,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.denominator
  · simpa only [Window.ofOld,guardA,Target830.Count.guardA,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.a
  · simpa only [Window.ofOld,guardC,Target830.Count.guardC,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.c
  · simpa only [Window.ofOld,guardJ,Target830.Count.guardJ,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.j
  · simpa only [Window.ofOld,guardTLo,Target830.Count.guardTLo,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cutoff_lower
  · simpa only [Window.ofOld,guardTHi,Target830.Count.guardTHi,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cutoff_upper
  · simpa only [Window.ofOld,guardRLo,Target830.Count.guardRLo,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cross_lower
  · simpa only [Window.ofOld,guardRHi,Target830.Count.guardRHi,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.cross_upper
  · simpa only [Window.ofOld,guardMLo,Target830.Count.guardMLo,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.plain_lower
  · simpa only [Window.ofOld,guardMHi,Target830.Count.guardMHi,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.plain_upper
  · simpa only [Window.ofOld,guardWidth,Target830.Count.guardWidth,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.selected_lower
  · simpa only [Window.ofOld,guardTail,Target830.Count.guardTail,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.tail
  · simpa only [Window.ofOld,guardMonotone,Target830.Count.guardMonotone,
      Plane.ofOld_lambda,Plane.ofOld_B] using h.monotone

end
end OAI.SevenEighths.MainCount
end

/- Original module: Candidate.Uneven.MainCountGeometry. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.MainCountArithmetic
open Target830
variable (P : MainCount.Plane)

theorem tN_formula (δ p : ℝ) :
    tN P δ p = Target830.Count.affineTNum P.lambda P.B δ p / Target830.Count.affineJ P.lambda δ p := by
  unfold tN numT JN DN aN cN Target830.Count.affineTNum Target830.Count.affineJ Target830.Count.affineU
    Target830.Count.affineD Target830.Count.affineA Target830.Count.affineC
  congr 1
  ring

theorem RNew_formula (δ p : ℝ) :
    RNew P δ p = Target830.Count.affineR P.lambda P.B δ p := by
  unfold RNew JN DN aN cN Target830.Count.affineR Target830.Count.affineJ Target830.Count.affineU
    Target830.Count.affineD Target830.Count.affineA Target830.Count.affineC
  ring

theorem crossing_mul (δ p : ℝ) (hD : DN P p ≠ 0)
    (hJ : Target830.Count.affineJ P.lambda δ p ≠ 0) :
    rN P p (tN P δ p) * (Target830.Count.affineD P.lambda p * Target830.Count.affineJ P.lambda δ p) =
      Target830.Count.affineRNum P.lambda P.B δ p := by
  have hr : rN P p (tN P δ p)*DN P p =
      aN P p*tN P δ p+2*p*P.B/P.lambda-p := div_mul_cancel₀ _ hD
  have ht : tN P δ p * Target830.Count.affineJ P.lambda δ p = Target830.Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula]
    exact div_mul_cancel₀ _ hJ
  change rN P p (tN P δ p)*(DN P p*Target830.Count.affineJ P.lambda δ p)=_
  calc
    _ = (aN P p*tN P δ p+2*p*P.B/P.lambda-p)*Target830.Count.affineJ P.lambda δ p := by rw [←hr];ring
    _ = aN P p*(tN P δ p*Target830.Count.affineJ P.lambda δ p)+
        (2*p*P.B/P.lambda-p)*Target830.Count.affineJ P.lambda δ p := by ring
    _ = _ := by rw [ht];rfl

theorem plain_mul (δ p : ℝ) (hD : DN P p ≠ 0)
    (hJ : Target830.Count.affineJ P.lambda δ p ≠ 0) :
    (tN P δ p-rN P p (tN P δ p)) *
      (Target830.Count.affineD P.lambda p*Target830.Count.affineJ P.lambda δ p) =
      Target830.Count.affineMNum P.lambda P.B δ p := by
  have hr := crossing_mul P δ p hD hJ
  have ht : tN P δ p*Target830.Count.affineJ P.lambda δ p=Target830.Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula];exact div_mul_cancel₀ _ hJ
  unfold Target830.Count.affineMNum
  linear_combination Target830.Count.affineD P.lambda p*ht-hr

/-- Every certified window supplies exactly the geometric and old-tail gates
of the actual affine detector count. -/
theorem admissible_geometry {δ p κ : ℝ} (h : MainCount.Admissible P δ p)
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hk : 7/10 ≤ κ) (hkhi : κ ≤ kappa0) :
    1 ≤ tN P δ p ∧ tN P δ p ≤ 3/2 ∧
      23/37 ≤ rN P p (tN P δ p) ∧ rN P p (tN P δ p) ≤ 1 ∧
      MainCount.lowerPlain P+1/100000 ≤ tN P δ p-rN P p (tN P δ p) ∧
      MainCountArithmetic.oldPlainExp δ p κ MainCount.mHi ≤ shortNew P δ p (tN P δ p) := by
  have hD : 0 < Target830.Count.affineD P.lambda p := h.denominator
  have hJ : 0 < Target830.Count.affineJ P.lambda δ p := h.j
  have hD' : DN P p ≠ 0 := hD.ne'
  have hprod : 0 < Target830.Count.affineD P.lambda p*Target830.Count.affineJ P.lambda δ p := mul_pos hD hJ
  have ht : tN P δ p*Target830.Count.affineJ P.lambda δ p=Target830.Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula];exact div_mul_cancel₀ _ hJ.ne'
  have hr := crossing_mul P δ p hD' hJ.ne'
  have hm := plain_mul P δ p hD' hJ.ne'
  have htlo := h.cutoff_lower
  have hthi := h.cutoff_upper
  have hrlo := h.cross_lower
  have hrhi := h.cross_upper
  have hmlo := h.plain_lower
  simp only [MainCount.guardTLo,MainCount.guardTHi] at htlo hthi
  simp only [MainCount.guardRLo,MainCount.guardRHi] at hrlo hrhi
  unfold MainCount.guardMLo at hmlo
  have ht0 : 1 ≤ tN P δ p := by nlinarith only [ht,htlo,hJ]
  have ht1 : tN P δ p ≤ 3/2 := by nlinarith only [ht,hthi,hJ]
  have hr0 : 23/37 ≤ rN P p (tN P δ p) := by nlinarith only [hr,hrlo,hprod]
  have hr1 : rN P p (tN P δ p) ≤ 1 := by nlinarith only [hr,hrhi,hprod]
  rw [mul_assoc] at hmlo
  change 0 < Target830.Count.affineMNum P.lambda P.B δ p -
    max plainLower (MainCount.lowerPlain P+1/100000)*(Target830.Count.affineD P.lambda p*Target830.Count.affineJ P.lambda δ p) at hmlo
  have hhmax := le_max_right plainLower (MainCount.lowerPlain P+1/100000)
  have hhmax' := mul_le_mul_of_nonneg_right hhmax hprod.le
  have hm0 : MainCount.lowerPlain P+1/100000 ≤ tN P δ p-rN P p (tN P δ p) := by
    nlinarith only [hm,hmlo,hhmax',hprod]
  refine ⟨ht0,ht1,hr0,hr1,hm0,?_⟩
  have hR : RNew P δ p*Target830.Count.affineJ P.lambda δ p=Target830.Count.affineN P.lambda P.B δ p := by
    rw [RNew_formula]
    exact Target830.Count.affine_count_mul hJ.ne'
  have htail := h.tail
  unfold MainCount.guardTail at htail
  have hbound : 1-2*δ*MainCount.mHi-2*δ*p*widthLower ≤ RNew P δ p := by
    nlinarith only [htail,hR,hJ]
  have hk0 : 0 < 6*κ := by linarith
  have hcap : widthLower ≤ (1-2*MainCount.mHi)/(6*κ) := by
    rw [le_div_iff₀ hk0]
    have hid : 1-2*MainCount.mHi=6*kappa0*widthLower := by unfold MainCount.mHi Target830.Count.mHi;ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right hkhi (show (0:ℝ) ≤ 6*widthLower by norm_num [widthLower])
    nlinarith only [hh]
  have hstep : oldPlainExp δ p κ MainCount.mHi ≤ 1-2*δ*MainCount.mHi-2*δ*p*widthLower := by
    have hh := mul_le_mul_of_nonneg_left hcap (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hδ) hp)
    unfold oldPlainExp
    calc
      _ = 1-2*δ*MainCount.mHi-(2*δ*p*((1-2*MainCount.mHi)/(6*κ))) := by ring
      _ ≤ _ := sub_le_sub_left hh _
  have hmax := short_at_tN P (show JN P δ p ≠ 0 from hJ.ne') hD'
  rw [hmax]
  exact hstep.trans hbound

end OAI.SevenEighths.MainCountArithmetic
end
end

/- Original module: Candidate.Uneven.MainCountChoice. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainDetectorCount
noncomputable section
open scoped Classical
open Target830

def window (stage : MainCount.Stage) : Fin 15 → MainCount.Window :=
  ![MainCount.Window.ofOld Count.window0,MainCount.Window.ofOld Count.window1,MainCount.Window.ofOld Count.window2,MainCount.Window.ofOld Count.window3,MainCount.Window.ofOld Count.window4,MainCount.Window.ofOld Count.window5,MainCount.Window.ofOld Count.window6,MainCount.Window.ofOld Count.window7,MainCount.Window.ofOld Count.window8,MainCount.Window.ofOld Count.window9,MainCount.window10 stage,MainCount.window11 stage,MainCount.window12 stage,MainCount.window13 stage,MainCount.window14 stage]

theorem window_admissible (stage : MainCount.Stage) (i : Fin 15) {d p : ℝ}
    (ha : (window stage i).Available d p) : MainCount.Admissible (window stage i).plane d p := by
  fin_cases i
  · exact MainCount.Window.ofOld_admissible Count.window0 (Count.window0_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window1 (Count.window1_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window2 (Count.window2_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window3 (Count.window3_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window4 (Count.window4_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window5 (Count.window5_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window6 (Count.window6_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window7 (Count.window7_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window8 (Count.window8_admissible d p ha)
  · exact MainCount.Window.ofOld_admissible Count.window9 (Count.window9_admissible d p ha)
  · exact MainCount.window10_admissible stage d p ha
  · exact MainCount.window11_admissible stage d p ha
  · exact MainCount.window12_admissible stage d p ha
  · exact MainCount.window13_admissible stage d p ha
  · exact MainCount.window14_admissible stage d p ha

theorem window_supported (stage : MainCount.Stage) (i : Fin 15) :
    stage.Supports (window stage i).plane := by
  fin_cases i <;> simp [window,MainCount.Window.ofOld,MainCount.Stage.Supports,
    MainCount.Plane.ofOld,Count.window0,Count.window1,Count.window2,Count.window3,Count.window4,Count.window5,Count.window6,Count.window7,Count.window8,Count.window9,MainCount.window10,MainCount.window11,MainCount.window12,MainCount.window13,MainCount.window14]

theorem attained (stage : MainCount.Stage) (κ d p : ℝ) :
    MainCount.count stage κ d p=Count.oldCount κ d p ∨
      ∃i : Fin 15,(window stage i).Available d p ∧
        MainCount.count stage κ d p=Count.affineR (window stage i).plane.lambda (window stage i).plane.B d p := by
  rcases MainCount.count_attained stage κ d p with hold | ⟨b,hb,ha,he⟩
  · rcases Target830.Physical.DetectorCount.attained κ d p with hh | ⟨i,ha,he⟩
    · exact Or.inl (hold.trans hh)
    · right
      fin_cases i
      · exact ⟨0,ha,hold.trans he⟩
      · exact ⟨1,ha,hold.trans he⟩
      · exact ⟨2,ha,hold.trans he⟩
      · exact ⟨3,ha,hold.trans he⟩
      · exact ⟨4,ha,hold.trans he⟩
      · exact ⟨5,ha,hold.trans he⟩
      · exact ⟨6,ha,hold.trans he⟩
      · exact ⟨7,ha,hold.trans he⟩
      · exact ⟨8,ha,hold.trans he⟩
      · exact ⟨9,ha,hold.trans he⟩
  · right
    simp only [MainCount.branches,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with hb | hb | hb | hb | hb <;> subst b
    · exact ⟨10,ha,he⟩
    · exact ⟨11,ha,he⟩
    · exact ⟨12,ha,he⟩
    · exact ⟨13,ha,he⟩
    · exact ⟨14,ha,he⟩

def choice (stage : MainCount.Stage) (κ d p : ℝ) : Option (Fin 15) :=
  if hh : MainCount.count stage κ d p=Count.oldCount κ d p then none
  else some (Classical.choose ((attained stage κ d p).resolve_left hh))

theorem choice_none (stage : MainCount.Stage) {κ d p : ℝ}
    (hh : choice stage κ d p=none) : MainCount.count stage κ d p=Count.oldCount κ d p := by
  by_cases he : MainCount.count stage κ d p=Count.oldCount κ d p
  · exact he
  · simpa [choice,he] using hh

theorem choice_some (stage : MainCount.Stage) {κ d p : ℝ} {i : Fin 15}
    (hh : choice stage κ d p=some i) : (window stage i).Available d p ∧
      MainCount.count stage κ d p=Count.affineR (window stage i).plane.lambda (window stage i).plane.B d p := by
  by_cases he : MainCount.count stage κ d p=Count.oldCount κ d p
  · simp [choice,he] at hh
  · have hi : Classical.choose ((attained stage κ d p).resolve_left he)=i := by
      simpa [choice,he] using hh
    rw [←hi]
    exact Classical.choose_spec ((attained stage κ d p).resolve_left he)

def cutoff (stage : MainCount.Stage) (d p κ : ℝ) : ℝ :=
  match choice stage κ d p with
  | none => Cycle25DetectorRowCount.cutoff d p κ
  | some i => MainCountArithmetic.tN (window stage i).plane d p

theorem cutoff_bounds (stage : MainCount.Stage) {d p κ : ℝ}
    (hd : 0 ≤ d) (hdhi : d ≤ 3/4) (hp : 0 ≤ p) (hphi : p ≤ 1/2)
    (hk : 7/10 ≤ κ) (hkhi : κ ≤ kappa0) :
    1 ≤ cutoff stage d p κ ∧ cutoff stage d p κ ≤ 3/2 := by
  unfold cutoff
  split <;> rename_i hh
  · exact Cycle25DetectorRowCount.cutoff_bounds hd hdhi hp hphi hk
      (hkhi.trans (by norm_num [kappa0]))
  · have hg := MainCountArithmetic.admissible_geometry _
      (window_admissible stage _ (choice_some stage hh).1) hd hp hk hkhi
    exact ⟨hg.1,hg.2.1⟩

end
end OAI.SevenEighths.MainDetectorCount
end

/- Original module: Candidate.Uneven.MainCountBalanced. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.MainDetectorCount
open Target830
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
  HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
  HeckeDetectorFixedAmplitudeCount Cycle25DetectorRawFiber

/-- The finite count envelope is realized on the original batches. Its cutoff stage
is selected from the old crossing and the ten certified windows before the
actual batch is supplied. All five genuine affine moments remain explicit. -/
theorem balanced (stage : MainCount.Stage)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      7/10≤κplain → κplain≤ kappa0 → 0<ν → ν≤1/100000 → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff stage (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c κ C height εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,∀P : MainCount.Plane, stage.Supports P →
        MainCount.lowerPlain P ≤ (B.fiber bin j J K hne).m →
        (B.fiber bin j J K hne).m ≤ MainCount.mHi →
        MainCount.AffineMarkedMoment (B.fiber bin j J K hne) P C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(MainCount.count stage κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := count_from_raw_moments_finite
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  obtain ⟨hold,hnew⟩ := hcount
  intro a ε T allowance κplain ν C height q i hU ha hd hε hε' hk hk1 hν hν1 hC hh hf
    Label Slot _ B hne hq hmom haff
  have hδ : 0<2*a-1 := by linarith
  have hqb := batch_mean_bounds B hne (by linarith) q hq
  have hp : 0≤ q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hp' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds stage hδ.le hd hp hp' hk hk1
  cases he : choice stage κplain (2*a-1) (q/(2*a-1)) with
  | none =>
    have hcut : cutoff stage (2*a-1) (q/(2*a-1)) κplain =
        Cycle25DetectorRowCount.cutoff (2*a-1) (q/(2*a-1)) κplain := by simp [cutoff,he]
    have hR : MainCount.count stage κplain (2*a-1) (q/(2*a-1)) =
        rowCount (2*a-1) (q/(2*a-1)) κplain := by
      exact (choice_none stage he).trans (DetectorAffineCount.rowCount_eq_countingR0 hk).symm
    have hmax := max_at_cutoff hδ.le hd hp hp' hk (hk1.trans (by norm_num [kappa0]))
    rw [←hcut] at hmax
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=> MainCount.count stage κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne'
        have hb' := hold a ε (cutoff stage (2*a-1) (q/(2*a-1)) κplain)
          T allowance κplain ν C height i hU ha hd hε (by linarith) ht.1 ht.2 hk
          (hk1.trans (by norm_num [kappa0])) hν hC hh hf (B.fiber bin j J K hne')
          (hmom bin j J K hne')
        rw [fiber_mean_eq B q hq bin j J K hne',hmax,←hR] at hb'
        exact hb')
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
  | some k =>
    have hs := choice_some stage he
    let P := (window stage k).plane
    have hgeom := MainCountArithmetic.admissible_geometry P (window_admissible stage k hs.1)
      hδ.le hp hk hk1
    have hcut : cutoff stage (2*a-1) (q/(2*a-1)) κplain=MainCountArithmetic.tN P (2*a-1) (q/(2*a-1)) := by
      simp [cutoff,he,P]
    have hmax := MainCountArithmetic.max_at_tN P
      (show MainCountArithmetic.JN P (2*a-1) (q/(2*a-1)) ≠ 0 from
        (window_admissible stage k hs.1).j.ne')
      (show MainCountArithmetic.DN P (q/(2*a-1)) ≠ 0 from
        (window_admissible stage k hs.1).denominator.ne')
    rw [MainCountArithmetic.RNew_formula,←hs.2,←hcut] at hmax
    rw [←hcut] at hgeom
    have hb := B.card_bound (fiberConstant C height K₀)
      (fun _=> MainCount.count stage κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)
      (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
        intro bin j J K hne'
        have hmean := fiber_mean_eq B q hq bin j J K hne'
        have hb' := hnew P a ε (cutoff stage (2*a-1) (q/(2*a-1)) κplain)
          T allowance κplain ν C height i hU ha hd hε hε' ht.1 ht.2 hk hk1 hν hν1 hC hh hf
          (B.fiber bin j J K hne')
          (by rw [hmean];exact hgeom.2.2.1)
          (by rw [hmean];exact hgeom.2.2.2.1)
          (by rw [hmean];exact hgeom.2.2.2.2.1)
          (by rw [hmean];exact hgeom.2.2.2.2.2)
          (hmom bin j J K hne') (haff bin j J K hne' P (window_supported stage k))
        rw [hmean,hmax] at hb'
        exact hb')
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb

end OAI.SevenEighths.MainDetectorCount
end
end

/- Original module: Candidate.Uneven.MainDetectorParameters. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.MainDetectorCount
open Target830
open scoped Classical BigOperators ContDiff
open Set Filter HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
  HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst Cycle25DetectorRowCount
  HeckeDetectorFixedAmplitudeCount Cycle25DetectorRawFiber

structure CountParameters (stage : MainCount.Stage) (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  c : ℝ
  k : ℝ
  c_pos : 0< c
  c_one : c≤1
  k_pos : 0< k
  affine : ∃K₀ : ℝ,0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance κplain ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤3/4 → 0≤ε → ε≤1/100000 →
      7/10≤κplain → κplain≤ kappa0 → 0<ν → ν≤1/100000 → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type} [Fintype Label]
        (B : Batch M H Label Slot U a ε (cutoff stage (2*a-1) (q/(2*a-1)) κplain) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Cycle25DetectorRawFiber.Moments (B.fiber bin j J K hne) κplain c k C height εm) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,∀P : MainCount.Plane, stage.Supports P →
        MainCount.lowerPlain P ≤ (B.fiber bin j J K hne).m →
        (B.fiber bin j J K hne).m ≤ MainCount.mHi →
        MainCount.AffineMarkedMoment (B.fiber bin j J K hne) P C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2*fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(MainCount.count stage κplain (2*a-1) (q/(2*a-1))+159*ε+εm+B.mesh+7*ν)

theorem exists_count_parameters (stage : MainCount.Stage)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) : Nonempty (CountParameters stage M H εm) := by
  obtain ⟨c,k,K,hc,hc1,hk,hK,hcount⟩ := balanced stage M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨c,k,hc,hc1,hk,⟨K,hK,hcount⟩⟩⟩


end OAI.SevenEighths.MainDetectorCount
end
end

/- Original module: Candidate.Uneven.EndpointCountParameters. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.UnevenEndpoint.Physical.DetectorCount
noncomputable section
variable [config : Configuration]
open HeckeFamily HeckeInverseAmplification

abbrev CountParameters (M : Ideal HeckeFamily.O) [NeZero M]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (εm : ℝ) :=
  MainDetectorCount.CountParameters config.stage M H εm

abbrev cutoff (d p κ : ℝ) : ℝ := MainDetectorCount.cutoff config.stage d p κ

theorem fresh_count_parameters (D : DetectorData) (F : SourceData) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact MainDetectorCount.exists_count_parameters config.stage F.modulus ⊤ le_top F.S
    F.w F.smooth F.compact F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

end
end OAI.SevenEighths.UnevenEndpoint.Physical.DetectorCount
end
