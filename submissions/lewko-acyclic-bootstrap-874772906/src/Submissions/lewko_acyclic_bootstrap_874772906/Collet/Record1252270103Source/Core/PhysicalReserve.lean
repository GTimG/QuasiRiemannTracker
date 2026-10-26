/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
A common positive reserve for the actual regular and family exponents. -/
import Submissions.lewko_acyclic_bootstrap_874772906.Collet.Record1252270103Source.Core.PhysicalScalarNone
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.Record1252270103Source.PhysicalScalar
noncomputable section
open Record1252270103Finite Record1252270103StepScalar High

def selectedGain (n low : Source) (high : Option Source) (b ν : ℝ) : ℝ :=
  match high with
  | none => Record12518109Gain.gain ν (b-2*(n.allowance:ℝ))
      (sourceFReal n low b-(n.allowance:ℝ))
  | some h => High.gain ν (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)
      (b-2*(n.allowance:ℝ)) (sourceFReal n low b-(n.allowance:ℝ))

def ActualGaps (n low : Source) (high : Option Source) (b ν reserve : ℝ) : Prop :=
  reserve≤1-sourceBase n low b ν+selectedGain n low high b ν-(n.highFee:ℝ) ∧
    ∀j, reserve≤familyGap n low b ν j

lemma reserve_of_cleared {δ d M x : ℝ} (hδ : 0<δ) (hd : 0<d) (hdM : d≤M)
    (hg : δ≤d*x) : δ/M≤x := by
  have hx : 0<x := (mul_pos_iff.mp (hδ.trans_le hg)).resolve_right (by intro h;linarith [h.1]) |>.2
  apply (div_le_iff₀ (hd.trans_le hdM)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hdM hx.le]

lemma family_reserve {n low : Source} {high : Option Source} {b ν δ M : ℝ}
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hδ : 0<δ) (hM : 12≤M)
    (hg : ∀j : Fin 3,δ≤sourceDensityWidthReal n low high b ν (familyIndex high j)) :
    ∀j,δ/M≤familyGap n low b ν j := by
  have ht : 0<densityDenom ν := by dsimp [densityDenom];linarith
  have htM : densityDenom ν≤M := by dsimp [densityDenom];linarith
  intro j
  apply reserve_of_cleared hδ ht htM
  rw [←source_family_identity n low high b ν ht.ne' j]
  exact hg j

theorem some_actual_reserve (n low h : Source) (b ν δ : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hL : 1<(h.L:ℝ)) (hδ : 0<δ)
    (hg : ∀j,δ≤sourceDensityWidthReal n low (some h) b ν j) :
    ActualGaps n low (some h) b ν (δ/(192*(h.L:ℝ))) := by
  have hf (k : Branch) : δ/(192*(h.L:ℝ))≤1-sourceBase n low b ν+
      facet ν (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) (b-2*(n.allowance:ℝ))
        (sourceFReal n low b-(n.allowance:ℝ)) k-(n.highFee:ℝ) := by
    apply reserve_of_cleared hδ (regular_denominator_positive hν0 hν1 hL k)
      (regular_denominator_upper hν0 hν1 hL k)
    rw [←source_some_facet_identity n low h b ν hν0 hν1 hL k]
    exact hg _
  constructor
  · dsimp only [selectedGain]
    rw [gain_eq_min_facets hν0 hν1 hL]
    obtain ⟨k,_,hk⟩ := (Finset.inf'_le_iff
      (f:=facet ν (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ) (b-2*(n.allowance:ℝ))
        (sourceFReal n low b-(n.allowance:ℝ))) Finset.univ_nonempty).mp (le_refl _)
    linarith [hf k]
  · exact family_reserve hν0 hν1 hδ (by linarith) (fun j=>hg _)

theorem none_actual_reserve (n low : Source) (b ν δ : ℝ)
    (hν0 : 1/2≤ν) (hν1 : ν≤3/4) (hδ : 0<δ)
    (hg : ∀j : Fin 6,δ≤sourceDensityWidthReal n low none b ν (Fin.castLE (by decide) j)) :
    ActualGaps n low none b ν (δ/1392) := by
  have hf (j : Fin 3) : δ/1392≤1-sourceBase n low b ν+
      naturalFacet ν (b-2*(n.allowance:ℝ))
        (sourceFReal n low b-(n.allowance:ℝ)) j-(n.highFee:ℝ) := by
    apply reserve_of_cleared hδ (natural_denominator_bounds hν0 hν1 j).1
      (natural_denominator_bounds hν0 hν1 j).2
    rw [←source_none_facet_identity n low b ν hν0 hν1 j]
    exact hg (Fin.castLE (by decide) j)
  constructor
  · have h0:=hf 0
    have h1:=hf 1
    have h2:=hf 2
    norm_num [naturalFacet] at h0 h1 h2
    have hm := le_min
      (show δ/1392-(1-sourceBase n low b ν-(n.highFee:ℝ))≤
        Record12518109Gain.phi ν*(b-2*(n.allowance:ℝ)) by linarith)
      (le_min (show δ/1392-(1-sourceBase n low b ν-(n.highFee:ℝ))≤
        Record12518109Gain.coeffA ν*(b-2*(n.allowance:ℝ))+
        Record12518109Gain.coeffB ν*(sourceFReal n low b-(n.allowance:ℝ)) by linarith)
        (show δ/1392-(1-sourceBase n low b ν-(n.highFee:ℝ))≤
        Record12518109Gain.coeffC ν*(sourceFReal n low b-(n.allowance:ℝ)) by linarith))
    dsimp only [selectedGain,Record12518109Gain.gain]
    linarith
  · apply family_reserve hν0 hν1 hδ (by norm_num : (12:ℝ)≤1392)
    intro j
    convert hg ⟨3+j.val,by omega⟩ using 1
    congr 1

/-- The reserve is chosen before every width, density and later finite family. -/
theorem nf_actual_uniform_reserve (n low : Source) (high : Option Source)
    (hv : SourceValid n low high) :
    ∃reserve : ℝ,0<reserve ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),ActualGaps n low high b ν reserve := by
  obtain ⟨δ,hδ,hall⟩:=nf_uniform_margin n low high hv
  have hq : (1/2:ℝ)≤n.q := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hv.2.2.2.2.2.1
    norm_num at hh
    exact hh
  cases high with
  | none =>
    refine ⟨δ/1392,by positivity,?_⟩
    intro b hb ν hν
    exact none_actual_reserve n low b ν δ (hq.trans hν.1) hν.2 hδ
      (fun j=>(hall b hb ν hν).2.2 _)
  | some h =>
    have hgood:=hv.2.2.2.2.2.2.2.2.2.2.2.1 h (by simp)
    have hL : 1<(h.L:ℝ) := by exact_mod_cast hgood.2.2.1
    refine ⟨δ/(192*(h.L:ℝ)),by positivity,?_⟩
    intro b hb ν hν
    exact some_actual_reserve n low h b ν δ (hq.trans hν.1) hν.2 hL hδ
      (hall b hb ν hν).2.2

theorem seed_actual_uniform_reserve (n low : Source) (hv : SeedSourceValid n low) :
    ∃reserve : ℝ,0<reserve ∧ ∀b∈Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ν∈Set.Icc (n.q:ℝ) (3/4),ActualGaps n low none b ν reserve := by
  obtain ⟨δ,hδ,hall⟩:=seed_uniform_margin n low hv
  have hq : (1/2:ℝ)≤n.q := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hv.2.2.2.2.2.1
    norm_num at hh
    exact hh
  refine ⟨δ/1392,by positivity,?_⟩
  intro b hb ν hν
  exact none_actual_reserve n low b ν δ (hq.trans hν.1) hν.2 hδ (hall b hb ν hν).2.2
end
end QRH.Record1252270103Source.PhysicalScalar
#print axioms QRH.Record1252270103Source.PhysicalScalar.nf_actual_uniform_reserve
#print axioms QRH.Record1252270103Source.PhysicalScalar.seed_actual_uniform_reserve
