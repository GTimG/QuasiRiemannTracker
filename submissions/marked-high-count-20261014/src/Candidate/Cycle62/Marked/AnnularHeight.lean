import Candidate.Cycle62.Marked.CommonSlotHeight
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace OAI.SevenEighths.Cycle62MarkedHeight
noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Set Complex

/-- A finite annular prime sum with its normalized ratios exposed. The
coefficient contains the arithmetic character and scale normalization. -/
def annularSum {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (W : ℝ→ℂ) (σ t : ℝ) : ℂ :=
  ∑p∈S,c p*W (ratio p)*(ratio p:ℂ)^(-(σ:ℂ)+(t:ℂ)*I)

def heightProfile (W : ℝ→ℂ) (y : ℝ) : ℂ := I*(Real.log y:ℂ)*W y

def commonProfile (W : ℝ→ℂ) (j : ℕ) (y : ℝ) : ℂ :=
  W y+(j:ℂ)*heightProfile W y

theorem commonProfile_support (W : ℝ→ℂ) (j : ℕ) :
    Function.support (commonProfile W j)⊆Function.support W := by
  intro y hy hzero
  exact hy (by simp [commonProfile,heightProfile,hzero])

theorem heightProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (heightProfile W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : heightProfile W =ᶠ[nhds (0:ℝ)] (fun _=>0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [heightProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx)
    exact (contDiffAt_const.mul hl).mul hW.contDiffAt

theorem commonProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (j : ℕ) :
    ContDiff ℝ ∞ (commonProfile W j) :=
  hW.add (contDiff_const.mul (heightProfile_smooth W a b ha hs hW))

theorem annularSum_profile {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (W : ℝ→ℂ) (σ t : ℝ) (j : ℕ) :
    annularSum S c ratio (commonProfile W j) σ t=
      annularSum S c ratio W σ t+(j:ℂ)*annularSum S c ratio (heightProfile W) σ t := by
  simp only [annularSum,commonProfile,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

private lemma phase_deriv (x σ t : ℝ) (hx : 0<x) :
    HasDerivAt (fun u : ℝ=>(x:ℂ)^(-(σ:ℂ)+(u:ℂ)*I))
      (I*(Real.log x:ℂ)*(x:ℂ)^(-(σ:ℂ)+(t:ℂ)*I)) t := by
  have hd := (((hasDerivAt_id (t:ℂ)).mul_const I).const_add (-(σ:ℂ))).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.comp_ofReal
  rw [←Complex.ofReal_log hx.le] at hh
  convert hh using 1 <;> simp only [id_eq] <;> ring

theorem annularSum_deriv {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (hratio : ∀p∈S,0<ratio p)
    (W : ℝ→ℂ) (σ t : ℝ) :
    HasDerivAt (annularSum S c ratio W σ)
      (annularSum S c ratio (heightProfile W) σ t) t := by
  have hd (p : Index) (hp : p∈S) :=
    (phase_deriv (ratio p) σ t (hratio p hp)).const_mul (c p*W (ratio p))
  convert HasDerivAt.sum (u:=S) hd using 1
  · ext u
    simp only [annularSum,Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [heightProfile]
    ring

theorem annularSum_continuous {Index : Type*} (S : Finset Index) (c : Index→ℂ)
    (ratio : Index→ℝ) (hratio : ∀p∈S,0<ratio p) (W : ℝ→ℂ) (σ : ℝ) :
    Continuous (annularSum S c ratio W σ) := by
  exact (show Differentiable ℝ (annularSum S c ratio W σ) from
    fun t=>(annularSum_deriv S c ratio hratio W σ t).differentiableAt).continuous

/-- Actual annular slot products can choose their common height row by row.
It is enough to know the usual fixed-height moment for the finite common
profiles `W*(1+j*i*log)`, at the same slot widths and arithmetic coefficients. -/
theorem annular_rowwise_energy {Row Slot Index : Type*} [DecidableEq Slot]
    (rows : Finset Row) (slots : Finset Slot) (N : ℕ) (hN : slots.card≤N)
    (pools : Slot→Finset Index) (c : Row→Slot→Index→ℂ)
    (ratio : Slot→Index→ℝ) (hratio : ∀s∈slots,∀p∈pools s,0<ratio s p)
    (W : ℝ→ℂ) (σ v : Slot→ℝ) (C : Row→ℂ)
    (a b E : ℝ) (hab : a≤b) (hE : 0≤E)
    (choice : Row→ℝ) (hchoice : ∀u∈rows,choice u∈Icc a b)
    (henergy : ∀j : Fin (N+1),∀t∈Icc a b,
      ∑u∈rows,‖C u*(∏s∈slots,
        annularSum (pools s) (c u s) (ratio s) (commonProfile W j.val) (σ s) (t+v s))‖^2≤E) :
    (∑u∈rows,‖C u*(∏s∈slots,
      annularSum (pools s) (c u s) (ratio s) W (σ s) (choice u+v s))‖^2)≤
      (1+2*(b-a))*commonProfileCost N*E := by
  apply rowwise_common_profile_energy rows slots N hN
    (fun u s t=>annularSum (pools s) (c u s) (ratio s) W (σ s) (t+v s))
    (fun u s t=>annularSum (pools s) (c u s) (ratio s) (heightProfile W) (σ s) (t+v s)) C
  · intro u hu s hs
    exact (annularSum_continuous (pools s) (c u s) (ratio s) (hratio s hs) W (σ s)).comp
      (continuous_id.add_const _)
  · intro u hu s hs
    exact (annularSum_continuous (pools s) (c u s) (ratio s) (hratio s hs)
      (heightProfile W) (σ s)).comp (continuous_id.add_const _)
  · intro u hu s hs t
    exact (annularSum_deriv (pools s) (c u s) (ratio s) (hratio s hs) W (σ s)
      (t+v s)).comp_add_const t (v s)
  · exact hab
  · exact hE
  · exact hchoice
  · intro j t ht
    simpa only [annularSum_profile] using henergy j t ht

end
end OAI.SevenEighths.Cycle62MarkedHeight
#print axioms OAI.SevenEighths.Cycle62MarkedHeight.annular_rowwise_energy
