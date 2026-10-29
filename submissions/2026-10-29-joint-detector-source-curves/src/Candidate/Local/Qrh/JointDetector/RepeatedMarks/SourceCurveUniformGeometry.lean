/- Copyright (c) 2026 Joseph Bebel. Apache-2.0. -/
import Candidate.Local.Qrh.JointDetector.RepeatedMarks.SourceCurveStepGeometry

namespace Qrh.JointDetector.RepeatedMarks.SourceCurve
noncomputable section
set_option autoImplicit false
open Set CurvedSourceStep SourceCurveSelector SourceCurveOpenGeometry

/-- Compact scalar geometry turns uniformly small source-coordinate and
secant errors into a literal finite source step. No source or analytic estimate
is assumed here. The forward step moves from the larger q to the smaller q. -/
theorem uniform_scalar_step_geometry {a b floor : ℝ} (hab : a ≤ b)
    (B L s n : ℝ → ℝ)
    (hB : ContinuousOn B (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hs : ContinuousOn s (Icc a b)) (hn : ContinuousOn n (Icc a b))
    (hfloor : 0 < floor)
    (hBp : ∀ x∈Icc a b, 0 < B x) (hBmax : ∀ x∈Icc a b, B x < 1)
    (hLmin : ∀ x∈Icc a b, (3/2:ℝ) ≤ L x)
    (hC : ∀ x∈Icc a b, 0 ≤ 6*B x-L x)
    (hnmin : ∀ x∈Icc a b, floor ≤ n x) (hnmax : ∀ x∈Icc a b, n x ≤ 3/4)
    (hgap : ∀ x∈Icc a b, 0 < L x-n x*(6*B x-L x))
    (hgates : ∀ x∈Icc a b, ∀ i, 0 < gate (B x) (L x) (s x) 0 (1/10) i)
    (hnear : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x∈Icc a b, ∀ y∈Icc a b, x < y → y-x ≤ δ →
      0 < L y-L x ∧ |B x-B y| ≤ η ∧ |L x-L y| ≤ η ∧
        |(B y-B x)/(L y-L x)-s y| ≤ η) :
    ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧
      ∀ x∈Icc a b, ∀ y∈Icc a b, x < y → y-x ≤ δ →
      ∃ g : ScalarStepGeometry (B y) (L y) (B x) (L x) (n y) floor,
        |g.secant-s y| ≤ ρ := by
  letI : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  obtain ⟨d,hd,hvalid⟩ := uniform_gates
    (fun x : Icc a b => B x) (fun x : Icc a b => L x) (fun x : Icc a b => s x) (1/10)
    hB.domRestrict hL.domRestrict hs.domRestrict (fun x => hgates x x.property)
  let K : Icc a b → ℝ := fun x => 2*n x/(L x-n x*(6*B x-L x))
  have hK : Continuous K := by
    apply (continuous_const.mul hn.domRestrict).div
      (hL.domRestrict.sub (hn.domRestrict.mul ((continuous_const.mul hB.domRestrict).sub hL.domRestrict)))
    intro x
    exact (hgap x x.property).ne'
  have hKp (x : Icc a b) : 0 < K x := by
    dsimp [K]
    exact div_pos (mul_pos (by norm_num) (hfloor.trans_le (hnmin x x.property))) (hgap x x.property)
  obtain ⟨xmax,_,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hK.continuousOn
  let M := K xmax+1
  have hM : 0 < M := by dsimp [M]; linarith [hKp xmax]
  have hKM (x : Icc a b) : K x ≤ M := by
    have hh := hmax (mem_univ x)
    change K x ≤ K xmax at hh
    dsimp [M]
    linarith
  intro ρ hρ
  let η := min ρ (min (d/(M+1)) (floor/(10*(M+1))))
  have hη : 0 < η := lt_min hρ (lt_min (by positivity) (by positivity))
  have hηρ : η ≤ ρ := min_le_left _ _
  have hηd : η*(M+1) ≤ d := by
    apply (le_div_iff₀ (by linarith : 0 < M+1)).1
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hηf : η*(M+1) ≤ floor/10 := by
    have hh : η ≤ floor/(10*(M+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 10*(M+1))).1 hh
    nlinarith
  have hηd' : η ≤ d := by nlinarith [mul_pos hη hM]
  obtain ⟨δ,hδ,hstep⟩ := hnear η hη
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hxy hsmall
  obtain ⟨hΔ,hBB,hLL,hss⟩ := hstep x hx y hy hxy hsmall
  let A := amplitude (L y) (6*B y-L y) (n y) (L y-L x)
  have hny : 0 < n y := hfloor.trans_le (hnmin y hy)
  have hA : 0 < A := amplitude_pos hny hΔ (hgap y hy)
  have hLclose : L y-L x ≤ η := by linarith [(abs_le.mp hLL).1]
  have hAid : A=K ⟨y,hy⟩*(L y-L x) := by dsimp [A,K,amplitude]; ring
  have hAM : A ≤ M*η := by
    rw [hAid]
    exact (mul_le_mul_of_nonneg_right (hKM ⟨y,hy⟩) hΔ.le).trans
      (mul_le_mul_of_nonneg_left hLclose hM.le)
  have hAd : A ≤ d := by nlinarith [mul_pos hη hM]
  have hAf : A ≤ floor/10 := by nlinarith
  let σ := (B y-B x)/(L y-L x)
  let e : Perturbation := ((B x-B y,L x-L y),(σ-s y,A))
  have he : dist e zeroPerturbation ≤ d := by
    simp only [e,zeroPerturbation,Prod.dist_eq,Real.dist_eq,sub_zero]
    exact max_le (max_le (hBB.trans hηd') (hLL.trans hηd'))
      (max_le (hss.trans hηd') (by simpa only [abs_of_pos hA] using hAd))
  have hg := hvalid ⟨y,hy⟩ e he
  dsimp [e] at hg
  rw [show B y+(B x-B y)=B x by ring,
      show L y+(L x-L y)=L x by ring,
      show s y+(σ-s y)=σ by ring] at hg
  have hpay : 5*A ≤ n y*(L x-1) := by
    have hh := mul_le_mul_of_nonneg_right (hnmin y hy) (by linarith [hLmin x hx] : 0 ≤ L x-1)
    nlinarith [hLmin x hx]
  let g := scalarStepGeometry_of_gates (hBp y hy) (hBmax y hy)
    (by linarith [hLmin y hy]) hΔ (hC y hy) hny (hgap y hy)
    hfloor (hnmin y hy) (hnmax y hy) hg hpay
  refine ⟨g,?_⟩
  change |(B y-B x)/(L y-L x)-s y| ≤ ρ
  exact hss.trans hηρ

end
end Qrh.JointDetector.RepeatedMarks.SourceCurve
#print axioms Qrh.JointDetector.RepeatedMarks.SourceCurve.uniform_scalar_step_geometry
