/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.High.Algebra
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.ChainCheck

/-!
# High.Gates

The HIGH child of every stage of the 256-stage chain (`Anchor.ChainData`, `Anchor.ChainCheck`):
for every `n < 256` and every `r ∈ [left n, R n]` the stage gates `Stg.Hyp` hold for
`chainStg n r = (R n, gain n, cut n, a0 n, a1 n, r / R n)`, hence

* `chain_detEx_le`: every HIGH class `(ν, e)` (`cut n ≤ ν ≤ 3/4`, `0 ≤ e ≤ ν`) has the cutoff
  `w = fw … r ν ∈ [2/3, 79/100]` with detector excess `≤ u`;
* `chain_highPrice_le`: `highPriceF (a0 n) (a1 n) (cut n) r s H ≤ u` with
  `s = fs (R n) (gain n) (cut n) r`, `H = fH (R n) r`, `u = fu (R n) r`.

The gates are checked by `ChainCheck` at the two endpoints only; gates 1, 9, 10 are affine in `r`,
gate 12 is affine after multiplication by `H`, and gate 11 does not depend on `r` (`g k = H w_b`).
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.High
noncomputable section
open Qrh.TwoSlot.AnchorExtension ChainData ChainCheck

/-- Positivity of an affine function between two points where it is positive. -/
theorem pos_of_affine {f : ℝ → ℝ} (hf : ∀ x, f x = f 0 + (f 1 - f 0) * x) {a b x : ℝ}
    (hab : a < b) (hx1 : a ≤ x) (hx2 : x ≤ b) (ha : 0 < f a) (hb : 0 < f b) : 0 < f x := by
  rw [hf] at ha hb ⊢
  exact affine_pos_of_endpoints hab hx1 hx2 ha hb

/-- Stage data of chain stage `n` at the free width `r`. -/
def chainStg (n : ℕ) (r : ℝ) : Stg := ⟨R n, gain n, cut n, a0 n, a1 n, r / R n⟩

section
variable (n : ℕ) (hn : n < 256)
include hn

theorem chain_R_ne (r : ℝ) : (chainStg n r).R ≠ 0 := (R_pos n hn).ne'

theorem chainStg_r (r : ℝ) : (chainStg n r).r = r := by
  have := R_pos n hn
  simp only [Stg.r, chainStg]; field_simp

theorem chainStg_s (r : ℝ) : (chainStg n r).s = fs (R n : ℝ) (gain n) (cut n) r := by
  have hR := R_pos n hn
  have hk : (0 : ℝ) < cut n := by linarith [(cut_bounds n hn).2.1]
  simp only [Stg.s, Stg.u, chainStg, fs, fS, fY, fu]
  field_simp
  ring

theorem chainStg_u (r : ℝ) : (chainStg n r).u = fu (R n : ℝ) r := by
  simp only [Stg.u, chainStg, fu]

theorem chainStg_H (r : ℝ) : (chainStg n r).H = fH (R n : ℝ) r := by
  simp only [chainStg, fH]

theorem chainStg_g (r ν : ℝ) :
    (chainStg n r).g ν = fg (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r ν := by
  have e1 := chainStg_r n hn r
  have e2 := chainStg_s n hn r
  have e3 := chainStg_u n hn r
  have e4 := chainStg_H n hn r
  simp only [Stg.g, Stg.D]
  rw [e1, e2, e3, e4]
  simp only [fg]
  rfl

theorem chainStg_w (r ν : ℝ) :
    (chainStg n r).w ν = fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r ν := by
  simp only [Stg.w]
  rw [chainStg_g n hn, chainStg_H n hn]
  simp only [fw]

theorem chainStg_F0 (r : ℝ) :
    (chainStg n r).F0 = fF0 (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) := by
  simp only [Stg.F0, Stg.wb, Stg.D, chainStg, fF0, fwb]

theorem chainStg_gate9 (r : ℝ) :
    (chainStg n r).gate9 = r / 2 - fs (R n : ℝ) (gain n) (cut n) r
      - 3 / 2 * (5 / 6 - (cut n : ℝ)) * (fu (R n : ℝ) r / ((cut n : ℝ) * cut n))
        / (1 / 2 - (a1 n : ℝ)) := by
  simp only [Stg.gate9, Stg.D]
  rw [chainStg_r n hn, chainStg_s n hn, chainStg_u n hn]
  simp only [chainStg]

end

/-- `g k = H w_b` for every `r` (the algebraic form of `ChainCheck.g_identity`). -/
theorem Stg.g_k (d : Stg) (hR : d.R ≠ 0) (hk : d.k ≠ 0) (hD : d.D ≠ 0) :
    d.g d.k = d.H * d.wb := by
  unfold Stg.g Stg.wb
  rw [mul_div_assoc']
  congr 1
  unfold Stg.r Stg.s
  field_simp
  ring

theorem left_pos (n : ℕ) (hn : n < 256) : (0 : ℝ) < left n := by
  have hn' : (n : ℚ) < 256 := by exact_mod_cast hn
  have : (0 : ℚ) < left n := by rw [left_eq]; linarith
  exact_mod_cast this

/-- The stage gates hold on the whole stage. -/
theorem chain_hyp (n : ℕ) (hn : n < 256) (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n) :
    (chainStg n r).Hyp := by
  have hR := R_pos n hn
  have hl := left_pos n hn
  have hlR := left_lt_R n
  have hr : 0 < r := hl.trans_le h1
  obtain ⟨hk3, hk1, hk2⟩ := cut_bounds n hn
  -- line facts
  have hline : (0 : ℝ) ≤ a1 n ∧ (a1 n : ℝ) ≤ 2 / 5 ∧ (a0 n : ℝ) - a1 n * R n ≤ gain n ∧
      (0 : ℝ) ≤ gain n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [a0_zero, a1_zero, gain_zero, Rat.cast_zero]
      norm_num
    · obtain ⟨hT, ha1, ha1', hg⟩ := chain_line n hpos hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hg0 := gain_succ_nonneg m (by omega)
      simp only [fline] at hg
      exact ⟨ha1.le, ha1'.le, by linarith, hg0⟩
  obtain ⟨ha1, ha1', hline', hg0⟩ := hline
  have hR1 : (R n : ℝ) < 1 := by
    have : R n < 1 := by
      rw [R_eq]; have : (0 : ℚ) ≤ n := by positivity
      linarith
    exact_mod_cast this
  -- endpoint facts as real statements at the two endpoints
  have hendL : (left n : ℚ) = left n ∨ (left n : ℚ) = R n := Or.inl rfl
  have hendR : (R n : ℚ) = left n ∨ (R n : ℚ) = R n := Or.inr rfl
  have eH : (chainStg n r).H = fH (R n : ℝ) r := chainStg_H n hn r
  have hH : 0 < (chainStg n r).H := by rw [eH]; unfold fH; exact div_pos hr hR
  refine ⟨hR, hH, ?_, by simp only [chainStg]; linarith, by simp only [chainStg]; linarith,
    ha1, ha1', hline', by simp only [chainStg]; linarith, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eH]; unfold fH; rw [div_le_one hR]; exact h2
  · -- gate 1
    rw [eH, chainStg_F0 n hn]
    have key := pos_of_affine (f := fun x => fH (R n : ℝ) x * fF0 (R n : ℝ) (gain n) (cut n)
      (a0 n) (a1 n) - 3 / 100000) (fun x => by simp only [fH]; ring) hlR h1 h2
      (gate1_real n hn _ hendL) (gate1_real n hn _ hendR)
    linarith
  · -- gate 9
    rw [chainStg_gate9 n hn]
    have key := pos_of_affine (f := fun x => x / 2 - fs (R n : ℝ) (gain n) (cut n) x
      - 3 / 2 * (5 / 6 - (cut n : ℝ)) * (fu (R n : ℝ) x / ((cut n : ℝ) * cut n))
        / (1 / 2 - (a1 n : ℝ)) - 1 / 10)
      (fun x => by simp only [fs, fS, fY, fu]; ring) hlR h1 h2
      (gate9_real n hn _ hendL) (gate9_real n hn _ hendR)
    linarith
  · -- gate 10
    rw [eH, chainStg_u n hn, chainStg_r n hn, chainStg_s n hn]
    have key := pos_of_affine (f := fun x => fH (R n : ℝ) x + fu (R n : ℝ) x - fH (R n : ℝ) x / 6
      - 1 / 15 - 3 / 4 * x - fs (R n : ℝ) (gain n) (cut n) x - 3 / 100)
      (fun x => by simp only [fH, fs, fS, fY, fu]; ring) hlR h1 h2
      (gate10_real n hn _ hendL) (gate10_real n hn _ hendR)
    linarith
  · -- gate 11: `w k = w_b + 10^-6` does not depend on `r`
    have hk0 : (cut n : ℝ) ≠ 0 := by linarith
    have hwk : ∀ x : ℝ, 0 < x → (chainStg n x).w (cut n) =
        fwb (R n : ℝ) (gain n) (a0 n) (a1 n) + 1 / 1000000 := by
      intro x hx
      have hHx : (chainStg n x).H ≠ 0 := (div_pos hx hR).ne'
      have hDx : (chainStg n x).D ≠ 0 := by
        show (1 / 2 - (a1 n : ℝ)) ≠ 0; linarith
      have := Stg.g_k (chainStg n x) (chain_R_ne n hn x) hk0 hDx
      simp only [Stg.w]
      rw [show (chainStg n x).k = cut n from rfl] at this
      rw [this, mul_div_cancel_left₀ _ hHx]
      simp only [Stg.wb, Stg.D, chainStg, fwb]
    have hR' : (0 : ℝ) < ((R n : ℚ) : ℝ) := hR
    have g11 := gate11_real n hn _ hendR
    rw [← chainStg_w n hn, hwk _ hR'] at g11
    show cutLo ≤ (chainStg n r).w (chainStg n r).k
    rw [show (chainStg n r).k = cut n from rfl, hwk r hr]
    unfold cutLo; linarith
  · -- gate 12, multiplied by `H`
    have hw : ∀ x : ℝ, 0 < x → (chainStg n x).H * (cutHi - (chainStg n x).w (3 / 4)) =
        fH (R n : ℝ) x * (79 / 100 - 1 / 1000000) - fg (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n)
          x (3 / 4) := by
      intro x hx
      have hHx : (chainStg n x).H ≠ 0 := (div_pos hx hR).ne'
      rw [chainStg_w n hn, chainStg_H n hn]
      rw [chainStg_H n hn] at hHx
      simp only [fw, cutHi]
      field_simp
      ring
    have hpos : ∀ x : ℝ, 0 < x → (0 < 79 / 100 - fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) x
        (3 / 4) ↔ 0 < fH (R n : ℝ) x * (79 / 100 - 1 / 1000000) -
          fg (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) x (3 / 4)) := by
      intro x hx
      have hHx : 0 < (chainStg n x).H := div_pos hx hR
      rw [← hw x hx, ← chainStg_w n hn]
      unfold cutHi
      constructor
      · intro h; exact mul_pos hHx h
      · intro h; exact pos_of_mul_pos_right h hHx.le
    have hRpos : (0 : ℝ) < ((R n : ℚ) : ℝ) := hR
    have hLpos : (0 : ℝ) < ((left n : ℚ) : ℝ) := hl
    have eL := (hpos _ hLpos).mp (gate12_real n hn _ hendL)
    have eR := (hpos _ hRpos).mp (gate12_real n hn _ hendR)
    have key := pos_of_affine (f := fun x => fH (R n : ℝ) x * (79 / 100 - 1 / 1000000) -
        fg (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) x (3 / 4))
      (fun x => by simp only [fH, fg, fs, fS, fY, fu]; ring) hlR h1 h2 eL eR
    rw [← hw r hr] at key
    have := pos_of_mul_pos_right key hH.le
    show (chainStg n r).w (3 / 4) ≤ cutHi
    linarith

/-- **HIGH child of chain stage `n`, per class.** -/
theorem chain_detEx_le (n : ℕ) (hn : n < 256) (r : ℝ) (h1 : (left n : ℝ) ≤ r) (h2 : r ≤ R n)
    {ν e : ℝ} (hν : (cut n : ℝ) ≤ ν) (hν' : ν ≤ 3 / 4) (he0 : 0 ≤ e) (he : e ≤ ν) :
    fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r ν ∈ cutoffs ∧
    detEx (a0 n) (a1 n) ν e (fw (R n : ℝ) (gain n) (cut n) (a0 n) (a1 n) r ν) r
      (fs (R n : ℝ) (gain n) (cut n) r) (fH (R n : ℝ) r) ≤ fu (R n : ℝ) r := by
  have h := chain_hyp n hn r h1 h2
  have m := Stg.w_mem h hν hν'
  have b := Stg.detEx_le h hν hν' he0 he
  rw [chainStg_w n hn] at m b
  rw [chainStg_r n hn, chainStg_s n hn, chainStg_H n hn, chainStg_u n hn] at b
  exact ⟨m, b⟩

/-- **The HIGH price of chain stage `n` is at most `u` on the whole stage.** -/
theorem chain_highPrice_le (n : ℕ) (hn : n < 256) (r : ℝ) (h1 : (left n : ℝ) ≤ r)
    (h2 : r ≤ R n) :
    highPriceF (a0 n) (a1 n) (cut n) r (fs (R n : ℝ) (gain n) (cut n) r) (fH (R n : ℝ) r) ≤
      fu (R n : ℝ) r := by
  have h := Stg.highPriceF_le (chain_hyp n hn r h1 h2)
  rw [chainStg_r n hn, chainStg_s n hn, chainStg_H n hn, chainStg_u n hn] at h
  exact h

/-- The thresholds satisfy the hypotheses of `highPrice`. -/
theorem chain_cut_mem (n : ℕ) (hn : n < 256) : (1 / 6 : ℝ) ≤ cut n ∧ (cut n : ℝ) ≤ 3 / 4 := by
  obtain ⟨-, h1, h2⟩ := cut_bounds n hn
  constructor <;> linarith

end
end Qrh.MarkedAnchor.High
