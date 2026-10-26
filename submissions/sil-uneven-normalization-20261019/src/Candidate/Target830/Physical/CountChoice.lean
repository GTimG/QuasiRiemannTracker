import Candidate.Target830.Physical.CountArithmetic
import Candidate.Target830.Count.Concrete
import Candidate.Cycle25.Assembly.Count.Optimization

/- Original module: Candidate.Target830.Physical.CountGeometry. -/
section

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.Target830.Physical.CountArithmetic
variable (P : Count.Plane)

theorem tN_formula (δ p : ℝ) :
    tN P δ p = Count.affineTNum P.lambda P.B δ p / Count.affineJ P.lambda δ p := by
  unfold tN numT JN DN aN cN Count.affineTNum Count.affineJ Count.affineU
    Count.affineD Count.affineA Count.affineC
  congr 1
  ring

theorem RNew_formula (δ p : ℝ) :
    RNew P δ p = Count.affineR P.lambda P.B δ p := by
  unfold RNew JN DN aN cN Count.affineR Count.affineJ Count.affineU
    Count.affineD Count.affineA Count.affineC
  ring

theorem crossing_mul (δ p : ℝ) (hD : DN P p ≠ 0)
    (hJ : Count.affineJ P.lambda δ p ≠ 0) :
    rN P p (tN P δ p) * (Count.affineD P.lambda p * Count.affineJ P.lambda δ p) =
      Count.affineRNum P.lambda P.B δ p := by
  have hr : rN P p (tN P δ p)*DN P p =
      aN P p*tN P δ p+2*p*P.B/P.lambda-p := div_mul_cancel₀ _ hD
  have ht : tN P δ p * Count.affineJ P.lambda δ p = Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula]
    exact div_mul_cancel₀ _ hJ
  change rN P p (tN P δ p)*(DN P p*Count.affineJ P.lambda δ p)=_
  calc
    _ = (aN P p*tN P δ p+2*p*P.B/P.lambda-p)*Count.affineJ P.lambda δ p := by rw [←hr];ring
    _ = aN P p*(tN P δ p*Count.affineJ P.lambda δ p)+
        (2*p*P.B/P.lambda-p)*Count.affineJ P.lambda δ p := by ring
    _ = _ := by rw [ht];rfl

theorem plain_mul (δ p : ℝ) (hD : DN P p ≠ 0)
    (hJ : Count.affineJ P.lambda δ p ≠ 0) :
    (tN P δ p-rN P p (tN P δ p)) *
      (Count.affineD P.lambda p*Count.affineJ P.lambda δ p) =
      Count.affineMNum P.lambda P.B δ p := by
  have hr := crossing_mul P δ p hD hJ
  have ht : tN P δ p*Count.affineJ P.lambda δ p=Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula];exact div_mul_cancel₀ _ hJ
  unfold Count.affineMNum
  linear_combination Count.affineD P.lambda p*ht-hr

/-- Every certified window supplies exactly the geometric and old-tail gates
of the actual affine detector count. -/
theorem admissible_geometry {δ p κ : ℝ} (h : Count.Admissible P δ p)
    (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hk : 7/10 ≤ κ) (hkhi : κ ≤ kappa0) :
    1 ≤ tN P δ p ∧ tN P δ p ≤ 3/2 ∧
      23/37 ≤ rN P p (tN P δ p) ∧ rN P p (tN P δ p) ≤ 1 ∧
      Count.lowerPlain P+1/100000 ≤ tN P δ p-rN P p (tN P δ p) ∧
      CountArithmetic.oldPlainExp δ p κ Count.mHi ≤ shortNew P δ p (tN P δ p) := by
  have hD : 0 < Count.affineD P.lambda p := h.denominator
  have hJ : 0 < Count.affineJ P.lambda δ p := h.j
  have hD' : DN P p ≠ 0 := hD.ne'
  have hprod : 0 < Count.affineD P.lambda p*Count.affineJ P.lambda δ p := mul_pos hD hJ
  have ht : tN P δ p*Count.affineJ P.lambda δ p=Count.affineTNum P.lambda P.B δ p := by
    rw [tN_formula];exact div_mul_cancel₀ _ hJ.ne'
  have hr := crossing_mul P δ p hD' hJ.ne'
  have hm := plain_mul P δ p hD' hJ.ne'
  have htlo := h.cutoff_lower
  have hthi := h.cutoff_upper
  have hrlo := h.cross_lower
  have hrhi := h.cross_upper
  have hmlo := h.plain_lower
  simp only [Count.guardTLo,Count.guardTHi] at htlo hthi
  simp only [Count.guardRLo,Count.guardRHi] at hrlo hrhi
  unfold Count.guardMLo at hmlo
  have ht0 : 1 ≤ tN P δ p := by nlinarith only [ht,htlo,hJ]
  have ht1 : tN P δ p ≤ 3/2 := by nlinarith only [ht,hthi,hJ]
  have hr0 : 23/37 ≤ rN P p (tN P δ p) := by nlinarith only [hr,hrlo,hprod]
  have hr1 : rN P p (tN P δ p) ≤ 1 := by nlinarith only [hr,hrhi,hprod]
  rw [mul_assoc] at hmlo
  change 0 < Count.affineMNum P.lambda P.B δ p -
    max plainLower (Count.lowerPlain P+1/100000)*(Count.affineD P.lambda p*Count.affineJ P.lambda δ p) at hmlo
  have hhmax := le_max_right plainLower (Count.lowerPlain P+1/100000)
  have hhmax' := mul_le_mul_of_nonneg_right hhmax hprod.le
  have hm0 : Count.lowerPlain P+1/100000 ≤ tN P δ p-rN P p (tN P δ p) := by
    nlinarith only [hm,hmlo,hhmax',hprod]
  refine ⟨ht0,ht1,hr0,hr1,hm0,?_⟩
  have hR : RNew P δ p*Count.affineJ P.lambda δ p=Count.affineN P.lambda P.B δ p := by
    rw [RNew_formula]
    exact Count.affine_count_mul hJ.ne'
  have htail := h.tail
  unfold Count.guardTail at htail
  have hbound : 1-2*δ*Count.mHi-2*δ*p*widthLower ≤ RNew P δ p := by
    nlinarith only [htail,hR,hJ]
  have hk0 : 0 < 6*κ := by linarith
  have hcap : widthLower ≤ (1-2*Count.mHi)/(6*κ) := by
    rw [le_div_iff₀ hk0]
    have hid : 1-2*Count.mHi=6*kappa0*widthLower := by unfold Count.mHi;ring
    rw [hid]
    have hh := mul_le_mul_of_nonneg_right hkhi (show (0:ℝ) ≤ 6*widthLower by norm_num [widthLower])
    nlinarith only [hh]
  have hstep : oldPlainExp δ p κ Count.mHi ≤ 1-2*δ*Count.mHi-2*δ*p*widthLower := by
    have hh := mul_le_mul_of_nonneg_left hcap (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hδ) hp)
    unfold oldPlainExp
    calc
      _ = 1-2*δ*Count.mHi-(2*δ*p*((1-2*Count.mHi)/(6*κ))) := by ring
      _ ≤ _ := sub_le_sub_left hh _
  have hmax := short_at_tN P (show JN P δ p ≠ 0 from hJ.ne') hD'
  rw [hmax]
  exact hstep.trans hbound

end OAI.SevenEighths.Target830.Physical.CountArithmetic
end
#print axioms OAI.SevenEighths.Target830.Physical.CountArithmetic.admissible_geometry
end

/- Original module: Candidate.Target830.Physical.CountChoice. -/
section

set_option autoImplicit false
noncomputable section
namespace OAI.SevenEighths.Target830.Physical.DetectorCount
open scoped Classical

def window : Fin 10 → Count.Window :=
  ![Count.window0,Count.window1,Count.window2,Count.window3,Count.window4,
    Count.window5,Count.window6,Count.window7,Count.window8,Count.window9]

theorem window_admissible (i : Fin 10) {δ p : ℝ} (ha : (window i).Available δ p) :
    Count.Admissible (window i).plane δ p := by
  fin_cases i
  · exact Count.window0_admissible δ p ha
  · exact Count.window1_admissible δ p ha
  · exact Count.window2_admissible δ p ha
  · exact Count.window3_admissible δ p ha
  · exact Count.window4_admissible δ p ha
  · exact Count.window5_admissible δ p ha
  · exact Count.window6_admissible δ p ha
  · exact Count.window7_admissible δ p ha
  · exact Count.window8_admissible δ p ha
  · exact Count.window9_admissible δ p ha

theorem attained (κ δ p : ℝ) :
    Count.count κ δ p=Count.oldCount κ δ p ∨
      ∃i : Fin 10,(window i).Available δ p ∧
        Count.count κ δ p=Count.affineR (window i).plane.lambda (window i).plane.B δ p := by
  rcases Count.count_attained κ δ p with hh | ⟨b,hb,ha,he⟩
  · exact Or.inl hh
  · right
    simp [Count.branches] at hb
    rcases hb with hb|hb|hb|hb|hb|hb|hb|hb|hb|hb <;> subst b
    · exact ⟨0,ha,he⟩
    · exact ⟨1,ha,he⟩
    · exact ⟨2,ha,he⟩
    · exact ⟨3,ha,he⟩
    · exact ⟨4,ha,he⟩
    · exact ⟨5,ha,he⟩
    · exact ⟨6,ha,he⟩
    · exact ⟨7,ha,he⟩
    · exact ⟨8,ha,he⟩
    · exact ⟨9,ha,he⟩

def choice (κ δ p : ℝ) : Option (Fin 10) :=
  if hh : Count.count κ δ p=Count.oldCount κ δ p then none
  else some (Classical.choose ((attained κ δ p).resolve_left hh))

theorem choice_none {κ δ p : ℝ} (hh : choice κ δ p=none) :
    Count.count κ δ p=Count.oldCount κ δ p := by
  by_cases he : Count.count κ δ p=Count.oldCount κ δ p
  · exact he
  · simpa [choice,he] using hh

theorem choice_some {κ δ p : ℝ} {i : Fin 10} (hh : choice κ δ p=some i) :
    (window i).Available δ p ∧
      Count.count κ δ p=Count.affineR (window i).plane.lambda (window i).plane.B δ p := by
  by_cases he : Count.count κ δ p=Count.oldCount κ δ p
  · simp [choice,he] at hh
  · have hi : Classical.choose ((attained κ δ p).resolve_left he)=i := by
      simpa [choice,he] using hh
    rw [←hi]
    exact Classical.choose_spec ((attained κ δ p).resolve_left he)

def cutoff (δ p κ : ℝ) : ℝ :=
  match choice κ δ p with
  | none => Cycle25DetectorRowCount.cutoff δ p κ
  | some i => CountArithmetic.tN (window i).plane δ p

theorem cutoff_bounds {δ p κ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 3/4)
    (hp : 0 ≤ p) (hphi : p ≤ 1/2) (hk : 7/10 ≤ κ) (hkhi : κ ≤ kappa0) :
    1 ≤ cutoff δ p κ ∧ cutoff δ p κ ≤ 3/2 := by
  unfold cutoff
  split <;> rename_i hh
  · exact Cycle25DetectorRowCount.cutoff_bounds hδ hδhi hp hphi hk
      (hkhi.trans (by norm_num [kappa0]))
  · have hg := CountArithmetic.admissible_geometry _ (window_admissible _ (choice_some hh).1)
      hδ hp hk hkhi
    exact ⟨hg.1,hg.2.1⟩

end OAI.SevenEighths.Target830.Physical.DetectorCount
end
#print axioms OAI.SevenEighths.Target830.Physical.DetectorCount.attained
#print axioms OAI.SevenEighths.Target830.Physical.DetectorCount.cutoff_bounds
end
