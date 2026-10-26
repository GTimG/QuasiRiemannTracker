import Submissions.hailey_collet_1252270103.Record1252270103Bootstrap.PR67Source.Cycle63.Physical.FinalProfiles
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
namespace OAI.SevenEighths
end OAI.SevenEighths
open _root_.OAI _root_.OAI.SevenEighths
namespace Record1252270103Bootstrap.PR67
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle63HighProfiles
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Set CenteredMomentFiniteProfileExceptional CenteredMomentEnergyAllocatedProfiles
open CenteredMomentRetainedProfile CenteredMomentEnergyProfiles

/-- The entire Mellin budget is fixed before the moving profile and before the
high-row theorem selects its required decay order. -/
theorem fixed_mellin_budget (a b : ℝ) (ha : 0<a) :
    ∃ bound : ℕ→ℝ, (∀ k,0<bound k) ∧ ∀ n : ℕ,
      ∃ S : Finset (ℕ×ℕ), (0,0)∈S ∧
      ∀ W : 𝓢(ℝ,ℂ), Function.support (W:ℝ→ℂ)⊆Icc a b →
      sourceControl S W≤1 → ∀ k : ℕ, (k=2 ∨ k=n+2) →
      ∀ x ∈ Icc (-1:ℝ) 2, ∀ u : ℝ,
        (1+|u|)^k*‖mellin W ((x:ℂ)+u*Complex.I)‖≤bound k := by
  choose R C hC hbound using fun k : ℕ =>
    CubicReflectionKernel.mellin_strip_source_bound a b ha (-1) 2 k
  refine ⟨C,hC,?_⟩
  intro n
  let S := insert (0,0) (R 2 ∪ R (n+2))
  refine ⟨S,by simp [S],?_⟩
  intro W hs hnorm k hk x hx u
  have hsub : R k⊆S := by
    rcases hk with rfl | rfl
    · exact Finset.subset_union_left.trans (Finset.subset_insert _ _)
    · exact Finset.subset_union_right.trans (Finset.subset_insert _ _)
  have hle : sourceControl (R k) W≤ sourceControl S W :=
    Seminorm.le_def.mp (Finset.sup_mono hsub) W
  exact (hbound k W hs x hx u).trans
    ((mul_le_mul_of_nonneg_left (hle.trans hnorm) (hC k).le).trans_eq (mul_one _))

theorem high_strip_mem {a e x : ℝ} (ha : a≤1) (he : e≤1/1000)
    (hx : x∈Icc (1-a-6*e) 2) : x∈Icc (-1:ℝ) 2 := by
  exact ⟨by linarith [hx.1],hx.2⟩

def clippedControl {a b : ℝ} (ha : 0<a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (i : Fin 2) : ℝ :=
  sourceControl S ((retainedPair a b ha p U hU 0).profile i)

def normalizedPlains {a b : ℝ} (ha : 0<a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0<U i) : Profiles a b where
  profile := fun i => (clippedControl ha S p U hU i)⁻¹ • p.profile i
  support := by
    intro i x hx
    apply p.support i
    intro hw
    apply hx
    simp [hw]

theorem clippedControl_nonneg {a b : ℝ} (ha : 0<a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (i : Fin 2) :
    0≤ clippedControl ha S p U hU i := sourceControl_nonneg _ _

theorem normalizedPlains_clipped {a b : ℝ} (ha : 0<a) (S : Finset (ℕ×ℕ))
    (p : Profiles a b) (U : Fin 2→ℝ) (hU : ∀ i,0<U i)
    (hret : ∀ i,1≤U i*b) (i : Fin 2) :
    dilated ((normalizedPlains ha S p U hU).profile i) (clipDilation (U i)) =
      (normalizedProfile S ((retainedPair a b ha p U hU 0).profile i):ℝ→ℂ) := by
  have he := Cycle63FinalProfiles.actual_clipped_pair a b ha p U hU hret i
  funext x
  have hx := congrFun he x
  change (clippedControl ha S p U hU i)⁻¹ • p.profile i (clipDilation (U i)*x) = _
  simp only [normalizedProfile,smul_apply,clippedControl]
  rw [hx]
  rfl

theorem dilated_injective {W V : ℝ→ℂ} {c : ℝ} (hc : c≠0)
    (he : dilated W c=dilated V c) : W=V := by
  funext x
  have h := congrFun he (x/c)
  simpa [dilated,mul_div_cancel₀ _ hc] using h

theorem normalizedPlains_reconstruct {a b : ℝ} (ha : 0<a)
    (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S) (p : Profiles a b)
    (U : Fin 2→ℝ) (hU : ∀ i,0<U i) (hret : ∀ i,1≤U i*b) (i : Fin 2) :
    clippedControl ha S p U hU i • (normalizedPlains ha S p U hU).profile i =
      p.profile i := by
  have he := Cycle63FinalProfiles.actual_clipped_pair a b ha p U hU hret i
  by_cases hc : clippedControl ha S p U hU i=0
  · have hz : (retainedPair a b ha p U hU 0).profile i=0 :=
      sourceControl_zero S hS _ hc
    have hd : dilated (p.profile i) (clipDilation (U i))=dilated 0 (clipDilation (U i)) := by
      rw [←he,hz]
      rfl
    have hp : p.profile i=0 := by
      apply SchwartzMap.ext
      exact congrFun (dilated_injective (by
        have := clipDilation_ge_one (U i) (hU i)
        linarith) hd)
    simp [hc,hp]
  · simp [normalizedPlains,smul_smul,hc]

/-- Each plain is normalized separately. The discarded homogeneous product is
bounded by the original pair control, with no extra power of that control. -/
theorem fixed_clipped_normalization (a b : ℝ) (ha : 0<a) :
    ∃ bound : ℕ→ℝ, (∀ k,0<bound k) ∧ ∀ n : ℕ,
      ∃ S T : Finset (ℕ×ℕ), ∃ C : ℝ, (0,0)∈S ∧ 0<C ∧
      ∀ p : Profiles a b, ∀ U : Fin 2→ℝ, ∀ hU : ∀ i,0<U i,
      (∀ i,1≤U i*b) →
      clippedControl ha S p U hU 0*clippedControl ha S p U hU 1≤C*p.control T ∧
      (∀ i, clippedControl ha S p U hU i •
        (normalizedPlains ha S p U hU).profile i=p.profile i) ∧
      (∀ i, Function.support (dilated ((normalizedPlains ha S p U hU).profile i)
        (clipDilation (U i)))⊆Icc (a/max 1 b) b) ∧
      (∀ i, ContDiff ℝ ∞ (dilated ((normalizedPlains ha S p U hU).profile i)
        (clipDilation (U i)))) ∧
      (∀ i k, (k=2 ∨ k=n+2) → ∀ x ∈ Icc (-1:ℝ) 2, ∀ u : ℝ,
        (1+|u|)^k*‖mellin (dilated ((normalizedPlains ha S p U hU).profile i)
          (clipDilation (U i))) ((x:ℂ)+u*Complex.I)‖≤bound k) := by
  have ha' : 0<a/max 1 b := div_pos ha (zero_lt_one.trans_le (le_max_left _ _))
  obtain ⟨bound,hbound,hbudget⟩ := fixed_mellin_budget (a/max 1 b) b ha'
  refine ⟨bound,hbound,?_⟩
  intro n
  obtain ⟨S,hS,hmellin⟩ := hbudget n
  obtain ⟨T,C,hC,hcontrol⟩ := Cycle63FinalProfiles.clipped_pair_control a b ha S
  refine ⟨S,T,C,hS,hC,?_⟩
  intro p U hU hret
  have hsup (i : Fin 2) : Function.support
      (normalizedProfile S ((retainedPair a b ha p U hU 0).profile i):ℝ→ℂ)⊆
      Icc (a/max 1 b) b :=
    (normalizedProfile_support S _).trans ((retainedPair a b ha p U hU 0).support i)
  refine ⟨hcontrol p U hU,normalizedPlains_reconstruct ha S hS p U hU hret,?_,?_,?_⟩
  · intro i
    rw [normalizedPlains_clipped ha S p U hU hret i]
    exact hsup i
  · intro i
    exact dilated_contDiff _ (((normalizedPlains ha S p U hU).profile i).smooth ⊤) _
  · intro i k hk x hx u
    rw [normalizedPlains_clipped ha S p U hU hret i]
    exact hmellin _ (hsup i) (normalizedProfile_control S _) k hk x hx u

end
end OAI.SevenEighths.Cycle63HighProfiles

end Record1252270103Bootstrap.PR67
