/-
The native start of the selected-leaf line, without the density chain.

A self-contained copy of the continuous induction `curve_induction` (`arvi_ode_shape/Induction.lean`) and of the native
line `native_end` (`arvi_ode_shape/NativeCurve.lean`), with the same proofs. The originals sit behind
`arvi_ode_shape.Induction`, whose only heavy import, `arvi_density.Density.StepMarked`, serves the statement of
`ode_inequality_estimate` alone; importing them would put the density chain (`Density/*`, `Source/Hybrid*`, Collet's
PR 67 density lemmas) in the import closure of every module that uses `native_end`. This file imports only the native
step (Sil's cube-free step and provider) and PR 76's fourth-power source. When `Induction.lean` imports
`hailey_collet_1252270103.Record1252270103Source.Core.Contract` (which defines `GlobalSource`) instead of `StepMarked`,
this file can be replaced by `arvi_ode_shape.NativeCurve`.

From PR 76's fourth-power source `G(99999/100000, 93/25, 3/50)` (`face0_source`), the native cube-free step is valid
from every face `(B, Λ₀, c(Λ₀))` of the line `c(Λ) = 3/50 + (80/2297)(93/25 - Λ)` to every face at most `10⁻⁵` further
down, with the selection `a = 1/10`. So every face of the line, `Λ ∈ [5143/2000, 93/25]`, is proven by one induction; at
`Λ = 5143/2000` the cap is `1/10`.
-/
import Submissions.sil_density_split_20261026.Source.Assembly
import Submissions.sil_density_split_20261026.CubeFree.Assembly.Provider
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderGeoSupply
import Submissions.sil_density_split_20261026.CubeFree.Second.ProviderDiag9

set_option autoImplicit false

namespace QRH.ArviSelectedLeaf.Native
open Set OAI OAI.SevenEighths QRH.SilDensitySplit

/-- **Continuous induction.** A property that holds at the top `Λb` and passes from any point to every point at
most `h₀` below it holds on all of `[Λa, Λb]`. (Copy of `QRH.ArviOdeShape.curve_induction`.) -/
theorem curve_induction (P : ℝ → Prop) {Λa Λb h₀ : ℝ} (hh₀ : 0 < h₀) (htop : P Λb)
    (hstep : ∀ Λ₀ ∈ Icc Λa Λb, ∀ Λ ∈ Icc Λa Λb, Λ < Λ₀ → Λ₀ - Λ ≤ h₀ → P Λ₀ → P Λ) :
    ∀ Λ ∈ Icc Λa Λb, P Λ := by
  have key : ∀ n : ℕ, ∀ Λ ∈ Icc Λa Λb, Λb - n * h₀ ≤ Λ → P Λ := by
    intro n
    induction n with
    | zero =>
      intro Λ hΛ h
      have : Λ = Λb := le_antisymm hΛ.2 (by simpa using h)
      exact this ▸ htop
    | succ n ih =>
      intro Λ hΛ h
      by_cases hc : Λb - n * h₀ ≤ Λ
      · exact ih Λ hΛ hc
      · have hc' : Λ < Λb - n * h₀ := lt_of_not_ge hc
        have hn : (0:ℝ) ≤ n * h₀ := mul_nonneg (Nat.cast_nonneg n) hh₀.le
        have hcast : ((n + 1 : ℕ) : ℝ) * h₀ = n * h₀ + h₀ := by push_cast; ring
        rw [hcast] at h
        obtain ⟨Λ₀, hΛ₀def⟩ : ∃ Λ₀ : ℝ, Λ₀ = min (Λ + h₀) Λb := ⟨_, rfl⟩
        have hΛ₀a : Λa ≤ Λ₀ := hΛ₀def ▸ le_min (by linarith only [hΛ.1, hh₀]) (hΛ.1.trans hΛ.2)
        have hΛ₀ : Λ₀ ∈ Icc Λa Λb := ⟨hΛ₀a, hΛ₀def ▸ min_le_right _ _⟩
        have h1 : Λb - n * h₀ ≤ Λ₀ := hΛ₀def ▸ le_min (by linarith only [h]) (by linarith only [hn])
        have hlt : Λ < Λ₀ := hΛ₀def ▸ lt_min (by linarith only [hh₀]) (by linarith only [hc', hn])
        have hle : Λ₀ - Λ ≤ h₀ := by
          have := min_le_left (Λ + h₀) Λb
          rw [← hΛ₀def] at this
          linarith only [this]
        exact hstep Λ₀ hΛ₀ Λ hΛ hlt hle (ih Λ₀ hΛ₀ h1)
  intro Λ hΛ
  obtain ⟨n, hn⟩ := exists_nat_ge ((Λb - Λ) / h₀)
  refine key n Λ hΛ ?_
  have := (div_le_iff₀ hh₀).mp hn
  linarith only [this]

/-- Sil's generic native step with the diagonal supplier (as in PR 86's `ChainK15.nativeStep`). -/
theorem nativeInputs : CubeFree.NativeInputs := fun _ _ _ h =>
  ⟨4, CubeFree.Assembly.step_inputs_of_provider _ _ 4 (fun _ hleaf =>
    CubeFree.Second.Provider.contrary_raw_side_provider (CubeFree.stepGates_of_native h) 4 le_rfl hleaf
      (CubeFree.Second.ProviderDiag.diag_supply _))⟩

theorem nativeStep : NativeStepStatement :=
  fun p n a h hβ hp => CubeFree.native_step nativeInputs p n a h hβ hp

noncomputable section

/-- The native line: budget `99999/100000`, cap `c(Λ) = 3/50 + (80/2297)(93/25 - Λ)`. -/
def nB : ℝ := 99999/100000
def nCap (Λ : ℝ) : ℝ := 3/50 + 80/2297 * (93/25 - Λ)
def nFace (Λ : ℝ) : Face := ⟨nB, Λ, nCap Λ⟩

/-- The `cap` gate of a native step of length `d ≤ 10⁻⁵` from a parent of cap `c ∈ [3/50, 1/10]`. -/
theorem native_cap_aux {c d : ℝ} (hc0 : 3/50 ≤ c) (hc1 : c ≤ 1/10) (hd0 : 0 ≤ d) (hd1 : d ≤ 1/100000) :
    0 < c * (1 - 6 * (1/10) * (c + 80/2297 * d)) - (1 - 1/10) * (c + 80/2297 * d) := by
  have h1 := mul_nonneg (sub_nonneg.2 hc0) (sub_nonneg.2 hc1)
  have h2 := mul_le_mul_of_nonneg_right hc1 hd0
  linarith only [h1, h2, hc0, hd1]

/-- **The native generator**: one native step along the line, for every parent `Λ₀ ∈ [5143/2000, 93/25]` and
every step `0 < h ≤ 10⁻⁵` with the child on the line. -/
theorem native_gates {Λ₀ Λ : ℝ} (hΛ₀ : Λ₀ ∈ Icc (5143/2000 : ℝ) (93/25)) (hΛ : Λ ∈ Icc (5143/2000 : ℝ) (93/25))
    (hlt : Λ < Λ₀) (hle : Λ₀ - Λ ≤ 1/100000) : NativeGates (nFace Λ₀) (nFace Λ) (1/10) := by
  obtain ⟨a0, a1⟩ := hΛ₀
  obtain ⟨b0, b1⟩ := hΛ
  have hc0 : 3/50 ≤ nCap Λ₀ := by unfold nCap; linarith only [a1]
  have hc1 : nCap Λ₀ ≤ 1/10 := by unfold nCap; linarith only [a0]
  have hc' : nCap Λ = nCap Λ₀ + 80/2297 * (Λ₀ - Λ) := by unfold nCap; ring
  have hcy1 : nCap Λ ≤ 1/10 := by unfold nCap; linarith only [b0]
  have hcy0 : 3/50 ≤ nCap Λ := by unfold nCap; linarith only [b1]
  have hL0 : (0:ℝ) < Λ₀ := by linarith only [a0]
  have g1 : 0 < (1/10 : ℝ) - nativeK * (Λ₀ - Λ + (6 * nB - Λ₀) * (1/10)) / Λ₀ := by
    unfold nativeK nB; rw [sub_pos, div_lt_iff₀ hL0]; linarith only [a0, hle]
  have g2 : 0 < nCap Λ₀ * (1 - 6 * (1/10) * nCap Λ) - (1 - 1/10) * nCap Λ := by
    rw [hc']; exact native_cap_aux hc0 hc1 (sub_nonneg.2 hlt.le) hle
  have g3 : 0 < Λ - 2 - 9/2 * (1/10) := by linarith only [b0]
  have g4 : 0 < Λ - 1 - 4 * (1/10) := by linarith only [b0]
  have g5 : 0 < 3/2 * Λ - 5/2 - 9/2 * (1/10) := by linarith only [b0]
  have g6 : 0 < (1/6 : ℝ) - (1 + 3/2 * (1/10)) * nCap Λ := by linarith only [hcy1]
  have g7 : 0 < (1 : ℝ) - 6 * (1/10) * nCap Λ := by linarith only [hcy1]
  have g8 : 0 < (1 : ℝ) - nativeK * (6 * nB - Λ₀) / Λ₀ := by
    unfold nativeK nB; rw [sub_pos, div_lt_iff₀ hL0]; linarith only [a0]
  have g9 : nCap Λ₀ < 1/6 := by linarith only [hc1]
  have hB : nB < 1 := by unfold nB; norm_num
  have hcy : 0 < nCap Λ := by linarith only [hcy0]
  exact ⟨g1, g2, g3, g4, g5, g6, g7, g8, le_rfl, hB, g9, hcy, by norm_num, hlt⟩

/-- **Every face of the native line is proven**, from the fourth-power source, by one induction. -/
theorem native_sources (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    ∀ Λ ∈ Icc (5143/2000 : ℝ) (93/25), (nFace Λ).Source := by
  have htop : (nFace (93/25)).Source := by
    have h := face0_source hβ
    have e : nFace (93/25) = face0 := by
      simp only [nFace, nB, nCap, face0]; norm_num
    rw [e]; exact h
  exact curve_induction (fun Λ => (nFace Λ).Source) (by norm_num : (0:ℝ) < 1/100000) htop
    (fun Λ₀ hΛ₀ Λ hΛ hlt hle hsrc => nativeStep _ _ _ (native_gates hΛ₀ hΛ hlt hle) hβ hsrc)

/-- The end of the native line: `G(99999/100000, 5143/2000, 1/10)` (copy of `QRH.ArviOdeShape.native_end`). -/
theorem native_end (hβ : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    QRH.Record1252270103Source.GlobalSource (99999/100000) (5143/2000) (1/10) := by
  have h := native_sources hβ (5143/2000) ⟨le_rfl, by norm_num⟩
  have e : nCap (5143/2000) = 1/10 := by unfold nCap; norm_num
  simpa only [Face.Source, nFace, nB, e] using h

end

end QRH.ArviSelectedLeaf.Native
