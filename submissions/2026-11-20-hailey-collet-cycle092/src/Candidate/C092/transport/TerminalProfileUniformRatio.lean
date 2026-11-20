/- Copyright (c) 2026 Hailey Collet. Apache-2.0.
Uniform fixed smooth multiplier on the actual compact ratio bank. -/
import Candidate.C092.transport.TerminalProfileUniformMellin
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicProfiles
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.Cycle092.TerminalProfileUniform
noncomputable section
open scoped Classical SchwartzMap ContDiff BigOperators
open Set OAI OAI.SevenEighths CenteredMomentFiniteProfileExceptional HeckeDetectorDyadicProfiles

def ratioSchwartz (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V) (W : 𝓢(ℝ,ℂ))
    (a b : ℝ) (hs : Function.support (W:ℝ→ℂ) ⊆ Icc a b) (R : ℝ) : 𝓢(ℝ,ℂ) :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((ratioProfile_support V W R).trans hs)).toSchwartzMap (by
      unfold ratioProfile
      exact (hV.comp (contDiff_const.mul contDiff_id)).mul (W.smooth ⊤))

theorem ratio_seminorm_bound (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (a b : ℝ) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : 𝓢(ℝ,ℂ),
    ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Icc a b, ∀ R ∈ Icc (0:ℝ) 4,
    SchwartzMap.seminorm ℝ k n (ratioSchwartz V hV W a b hs R) ≤
      C*sourceControl (Finset.Iic (k,n)) W := by
  classical
  let F : (ℝ×ℝ)→ℝ→ℂ := fun p x => V (p.1*x)
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by dsimp [F,Function.uncurry]; fun_prop
  have hder (i : ℕ) : ∃ C : ℝ,0 < C ∧
      ∀ R ∈ Icc (0:ℝ) 4, ∀ x ∈ Icc a b, ‖iteratedFDeriv ℝ i (fun x => V (R*x)) x‖ ≤ C := by
    have hc := (section_iteratedDeriv_smooth F hF i).continuous.norm
    obtain ⟨M,hM⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).bddAbove_image
      (show ContinuousOn (fun p : (ℝ×ℝ)×ℝ => ‖iteratedDeriv i (F p.1) p.2‖)
        ((Icc (0:ℝ) 4 ×ˢ Icc (0:ℝ) 0) ×ˢ Icc a b) from hc.continuousOn)
    refine ⟨|M|+1,by positivity,?_⟩
    intro R hR x hx
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (hM (Set.mem_image_of_mem _ (show ((R,0),x) ∈
      (Icc (0:ℝ) 4 ×ˢ Icc (0:ℝ) 0) ×ˢ Icc a b from ⟨⟨hR,by simp⟩,hx⟩))).trans
      (by linarith [le_abs_self M])
  choose C hC hCb using hder
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*C i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hC i).le)
  refine ⟨B+1,by positivity,?_⟩
  intro W hs R hR
  have hctl := sourceControl_nonneg (Finset.Iic (k,n)) W
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro x
  change ‖x‖^k*‖iteratedDeriv n (ratioProfile V W R) x‖ ≤ _
  by_cases hx : x ∈ Icc a b
  · rw [←norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hmul := norm_iteratedFDeriv_mul_le (f := fun x => V (R*x)) (g := (W:ℝ→ℂ)) (hV.comp (contDiff_const.mul contDiff_id))
      (W.smooth ⊤) x (n := n) (by simp)
    apply (mul_le_mul_of_nonneg_left hmul (by positivity : 0 ≤ ‖x‖^k)).trans
    calc
      _ = ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*
          ‖iteratedFDeriv ℝ i (fun x => V (R*x)) x‖*
          (‖x‖^k*‖iteratedFDeriv ℝ (n-i) W x‖) := by rw [Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i:ℝ)*C i*
          sourceControl (Finset.Iic (k,n)) W := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hCb i R hR x hx) (by positivity)
        · exact (W.le_seminorm ℝ k (n-i) x).trans
            (Seminorm.le_def.mp (Finset.le_sup (f := schwartzSeminormFamily ℝ ℝ ℂ)
              (by simp : (k,n-i) ∈ Finset.Iic (k,n))) W)
        · positivity
        · exact mul_nonneg (Nat.cast_nonneg _) (hC i).le
      _ = B*sourceControl (Finset.Iic (k,n)) W := by rw [←Finset.sum_mul]
      _ ≤ (B+1)*sourceControl (Finset.Iic (k,n)) W :=
        mul_le_mul_of_nonneg_right (by linarith) (sourceControl_nonneg _ _)
  · have hz : iteratedDeriv n (ratioProfile V W R) x = 0 := by
      by_contra hn
      exact hx ((closure_minimal ((ratioProfile_support V W R).trans hs) isClosed_Icc)
        (CubicReflectionKernel.tsupport_iteratedDeriv_subset _ n (subset_tsupport _ hn)))
    rw [hz,norm_zero,mul_zero]
    positivity

/-- A finite control of the original profile pays the whole compact cofactor bank. -/
theorem ratio_controls (V : ℝ→ℂ) (hV : ContDiff ℝ ∞ V)
    (a b : ℝ) (T : Finset (ℕ×ℕ)) :
    ∃ S : Finset (ℕ×ℕ), (0,0) ∈ S ∧ T ⊆ S ∧ ∃ C : ℝ, 0 < C ∧
    ∀ W : 𝓢(ℝ,ℂ), ∀ hs : Function.support (W:ℝ→ℂ) ⊆ Icc a b,
    ∀ R ∈ Icc (0:ℝ) 4,
    sourceControl T (ratioSchwartz V hV W a b hs R) ≤ C*sourceControl S W := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨{(0,0)},by simp,by simp,1,zero_lt_one,by simp [sourceControl]⟩
  | @insert z T hz ih =>
    obtain ⟨S,hS,hTS,C,hC,hb⟩ := ih
    obtain ⟨D,hD,hd⟩ := ratio_seminorm_bound V hV a b z.1 z.2
    let S' := insert z (S ∪ Finset.Iic z)
    have hSS : S ⊆ S' := fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_left _ hx)
    have hIS : Finset.Iic z ⊆ S' := fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)
    refine ⟨S',hSS hS,?_,C+D,by positivity,?_⟩
    · exact Finset.insert_subset (Finset.mem_insert_self _ _) (hTS.trans hSS)
    · intro W hs R hR
      have hmono (A : Finset (ℕ×ℕ)) (hA : A ⊆ S') : sourceControl A W ≤ sourceControl S' W :=
        Seminorm.le_def.mp (Finset.sup_mono hA) W
      have hctl := sourceControl_nonneg S' W
      change (insert z T).sup (schwartzSeminormFamily ℝ ℝ ℂ) _ ≤ _
      rw [Finset.sup_insert,Seminorm.sup_apply]
      apply max_le
      · exact (hd W hs R hR).trans ((mul_le_mul_of_nonneg_left (hmono _ hIS) hD.le).trans (by nlinarith))
      · exact (hb W hs R hR).trans ((mul_le_mul_of_nonneg_left (hmono _ hSS) hC.le).trans (by nlinarith))

#print axioms ratio_seminorm_bound
#print axioms ratio_controls
end
end QRH.Cycle092.TerminalProfileUniform
