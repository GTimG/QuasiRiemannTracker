import Candidate.Cycle63.Physical.AllocationClipping

namespace Cycle63.Physical

noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths HeckeFamily
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentActiveDivisorShell
local notation "O" => ActualEisensteinCubic.O

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

def sourcePlainScales (s : Source ι) (second : Bool) : Fin 2 → ℝ :=
  if second then ![s.Y₁,s.Y₂] else ![s.X₁,s.X₂]

def sourcePositiveRow (s : Source ι) (second : Bool) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) (z : O) : ℂ :=
  allocatedPositiveRow s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((Ideal.absNorm I : ℝ)/s.P i)) s.P D a s.W₁ s.W₂
    (sourcePlainScales s second 0) (sourcePlainScales s second 1)

def plainClipAllowance (Z : ℝ) (b : Fin 2 → ℝ) : ℝ :=
  ∑ j, Real.logb Z (max 1 (b j))

def sourcePostClip (s : Source ι) (second : Bool) (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  negativeTotal (fun j => Real.logb Z (sourcePlainScales s second j)-
    actualPlainReduction Z D a j)

theorem source_post_clip_bound (s : Source ι) (second : Bool) (Z : ℝ) (hZ : 1 < Z)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (z : O) (b : Fin 2 → ℝ) (hX : ∀ j, 0 < sourcePlainScales s second j)
    (hs₁ : Function.support s.W₁ ⊆ Set.Iic (b 0))
    (hs₂ : Function.support s.W₂ ⊆ Set.Iic (b 1))
    (hn : sourcePositiveRow s second D a z ≠ 0) :
    sourcePostClip s second Z D a ≤ plainClipAllowance Z b :=
  actual_post_clipping_bound Z hZ s.η s.m s.A z s.t s.slots
    (fun i I => s.ν i I*s.W i ((Ideal.absNorm I : ℝ)/s.P i)) s.P D a s.W₁ s.W₂
    (sourcePlainScales s second) b hX hs₁ hs₂ hn

/-- The retained two-row scalar includes both actual changes of normalizer. -/
def sourceClippedPairWeight (s : Source ι) (v : Source κ) (secondS secondV : Bool)
    (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) : ℝ :=
  (1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*
    Z^((sourcePostClip s secondS Z D a+sourcePostClip v secondV Z D b)/2)

/-- Zero positive pairs contribute zero. The clipping cap is derived separately
for every surviving pair, after both signed rectangles have been split. -/
def nonzeroClippedPairWeight (s : Source ι) (v : Source κ) (secondS secondV : Bool)
    (Z : ℝ) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O) : ℝ :=
  if sourcePositiveRow s secondS D a zs ≠ 0 ∧ sourcePositiveRow v secondV D b zv ≠ 0
    then sourceClippedPairWeight s v secondS secondV Z D a b else 0

theorem nonzero_clipped_pair_le_raw (s : Source ι) (v : Source κ)
    (secondS secondV : Bool) (Z : ℝ) (hZ : 1 < Z) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (b : Allocation D (Finset.univ : Finset (κ ⊕ Fin 2))) (zs zv : O)
    (bs bv : Fin 2 → ℝ)
    (hXs : ∀ j, 0 < sourcePlainScales s secondS j)
    (hXv : ∀ j, 0 < sourcePlainScales v secondV j)
    (hs₁ : Function.support s.W₁ ⊆ Set.Iic (bs 0))
    (hs₂ : Function.support s.W₂ ⊆ Set.Iic (bs 1))
    (hv₁ : Function.support v.W₁ ⊆ Set.Iic (bv 0))
    (hv₂ : Function.support v.W₂ ⊆ Set.Iic (bv 1)) :
    nonzeroClippedPairWeight s v secondS secondV Z D a b zs zv ≤
      (1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*
        Z^((plainClipAllowance Z bs+plainClipAllowance Z bv)/2) := by
  unfold nonzeroClippedPairWeight
  split_ifs with hn
  · have hh₁ := source_post_clip_bound s secondS Z hZ D a zs bs hXs hs₁ hs₂ hn.1
    have hh₂ := source_post_clip_bound v secondV Z hZ D b zv bv hXv hv₁ hv₂ hn.2
    unfold sourceClippedPairWeight
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)) (by positivity)
  · positivity

/-- This is the residual divisor-dyad payment for the actual retained scalars.
The constant precedes every moving source, frequency and allocation. The
projector is not encoded as a divisor of the reconstructed frequency. -/
theorem paired_all_clipped_active_shell
    (N : ℕ) (hι : Fintype.card ι ≤ N) (hκ : Fintype.card κ ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Source ι) (v : Source κ) (secondS secondV : Bool)
      (bs bv : Fin 2 → ℝ),
      (∀ j, 0 < sourcePlainScales s secondS j) →
      (∀ j, 0 < sourcePlainScales v secondV j) →
      Function.support s.W₁ ⊆ Set.Iic (bs 0) →
      Function.support s.W₂ ⊆ Set.Iic (bs 1) →
      Function.support v.W₁ ⊆ Set.Iic (bv 0) →
      Function.support v.W₂ ⊆ Set.Iic (bv 1) →
      ∀ (Ds : Finset (Ideal O)), (∀ D∈Ds, Squarefree D) →
      ∀ (zs zv : ∀ D : Ideal O,
        Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)) →
        Allocation D (Finset.univ : Finset (κ ⊕ Fin 2)) → O)
      (T Z : ℝ), 1 ≤ T → 1 < Z →
      (∀ D∈Ds, T ≤ (Ideal.absNorm D : ℝ)) →
      (∀ D∈Ds, (Ideal.absNorm D : ℝ) < 2*T) →
      (∑ D∈Ds, ∑ a∈s.active D, ∑ b∈v.active D,
        nonzeroClippedPairWeight s v secondS secondV Z D a b (zs D a b) (zv D a b)) ≤
        C*(2*T)^(2*ε)*
          Z^((s.allowance Z+v.allowance Z+plainClipAllowance Z bs+plainClipAllowance Z bv)/2) := by
  obtain ⟨C,hC,hbound⟩ := paired_all_active_shell N hι hκ ε hε
  refine ⟨C,hC,?_⟩
  intro s v secondS secondV bs bv hXs hXv hs₁ hs₂ hv₁ hv₂ Ds hD zs zv T Z hT hZ hlo hhi
  let K : ℝ := Z^((plainClipAllowance Z bs+plainClipAllowance Z bv)/2)
  have hK : 0 ≤ K := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hh := hbound s v Ds hD T Z hT hZ hlo hhi
  calc
    _ ≤ ∑ D∈Ds, ∑ a∈s.active D, ∑ b∈v.active D,
        (1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*K :=
      Finset.sum_le_sum (fun D _ => Finset.sum_le_sum (fun a _ =>
        Finset.sum_le_sum (fun b _ => nonzero_clipped_pair_le_raw s v secondS secondV Z hZ
          D a b (zs D a b) (zv D a b) bs bv hXs hXv hs₁ hs₂ hv₁ hv₂)))
    _ = (∑ D∈Ds, ∑ a∈s.active D, ∑ b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))*K := by
      simp only [Finset.sum_mul]
    _ ≤ (C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2))*K :=
      mul_le_mul_of_nonneg_right hh hK
    _ = _ := by
      unfold K
      rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans hZ)]
      congr 2
      ring

end
end Cycle63.Physical
