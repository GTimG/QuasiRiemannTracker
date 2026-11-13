/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0. -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Inversion.InitialCanonicalState

/-!
# Inverse.InitGeometry

The geometry of the baseline's initial canonical state
(`InitialCanonicalStateWindow.actual_window_state`):

  `D = r + z - 2G`, `N = max 0 (D-B-v)`, `V = θ+v+2η`, `F = N+V`, `M = θ+H+2η`,
  `z_live = z - G`, `Q ≤ B-θ+G+3η`, `radialCenter m H θ D B ≤ 4η+τ`.

* `initial_geometry`: `N - z_live ≤ r - G + 3η`, `F ≤ r + z_live + 7η`, `z_live ≤ z`,
  `M ≤ 2F - m + 2η + τ` (so the Gauss row exponent is `2F - m` up to `O(η)`).
* `live_initial_margins`: the native margins at the initial state already follow from the
  gates on the LIVE width, `r + 2 z_live ≤ m - c₁`, `2r + 8 z_live ≤ 3m - c₂` (the overlap `G`
  cancels). This is the `u = 0` (insufficient live marks) branch of the selection.
* `selection_widths` / `child_exponent_identity`: after selecting width `u` the child has free
  width `N - z_live`, mark width `z_live - u`, physical radius `2F - M - 6u ≥ m - 6u - 2η - τ`,
  and prefactor `+` child budget equals `F` exactly.
-/

set_option autoImplicit false

namespace Qrh.MarkedAnchor.Inverse
noncomputable section

open OAI.SevenEighths.InverseMoment OAI.SevenEighths.InverseInitialProfile

/-- The initial canonical total exponent `F = N+V` of the window state. -/
def stateF (r z G B θ v η : ℝ) : ℝ := max 0 (r+z-2*G-B-v) + (θ+v+2*η)

/-- The initial Gauss row exponent `M`. -/
def stateM (θ H η : ℝ) : ℝ := θ+H+2*η

/-- The initial-state geometry and the row relation `M ≈ 2F - m`. -/
theorem initial_geometry (m r z G B θ v H η τ : ℝ)
    (hG : 0 ≤ G) (hP : -2*η ≤ B-θ) (hBv : 0 ≤ B+v)
    (hclip : max 0 (r+z-2*G-B-v) - (r+z-2*G-B-v) ≤ 3*η)
    (hcut : radialCenter m H θ (r+z-2*G) B ≤ 4*η+τ) :
    max 0 (r+z-2*G-B-v) - (z-G) ≤ r - G + 3*η ∧
    stateF r z G B θ v η ≤ r + (z-G) + 7*η ∧
    z - G ≤ z ∧
    stateM θ H η ≤ 2*stateF r z G B θ v η - m + 2*η + τ := by
  unfold stateF stateM
  unfold radialCenter at hcut
  have hmax := le_max_right 0 (r+z-2*G-B-v)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Native margins at the initial state from the gates on the live width only. -/
theorem live_initial_margins (m r z G B θ v H η τ Q c₁ c₂ : ℝ)
    (h₁ : r+2*(z-G) ≤ m-c₁) (h₂ : 2*r+8*(z-G) ≤ 3*m-c₂)
    (hG : 0 ≤ G) (hP : -2*η ≤ B-θ) (hQ : Q ≤ B-θ+G+3*η)
    (hc : 0 ≤ min c₁ c₂) (_hη : 0 ≤ η) (hηsmall : η ≤ min c₁ c₂/100)
    (hτ : τ ≤ min c₁ c₂/100)
    (hcut : radialCenter m H θ (r+z-2*G) B ≤ 4*η+τ) :
    CanonicalMargins (stateF r z G B θ v η) (stateM θ H η) Q (z-G) (3*min c₁ c₂/4) := by
  unfold CanonicalMargins stateF stateM
  unfold radialCenter at hcut
  have hmax := le_max_right 0 (r+z-2*G-B-v)
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

/-- Strict live gates with a reserve give the margins for small `η, τ`. -/
theorem live_initial_margins_of_strict (m r z G B θ v H η τ Q : ℝ)
    (h₁ : r+2*(z-G) < m) (h₂ : 2*r+8*(z-G) < 3*m)
    (hG : 0 ≤ G) (hP : -2*η ≤ B-θ) (hQ : Q ≤ B-θ+G+3*η) (hη : 0 ≤ η)
    (hηsmall : η ≤ min (m-r-2*(z-G)) (3*m-2*r-8*(z-G))/100)
    (hτ : τ ≤ min (m-r-2*(z-G)) (3*m-2*r-8*(z-G))/100)
    (hcut : radialCenter m H θ (r+z-2*G) B ≤ 4*η+τ) :
    CanonicalMargins (stateF r z G B θ v η) (stateM θ H η) Q (z-G)
      (3*min (m-r-2*(z-G)) (3*m-2*r-8*(z-G))/4) :=
  live_initial_margins m r z G B θ v H η τ Q _ _ (by linarith) (by linarith) hG hP hQ
    (le_min (by linarith) (by linarith)) hη hηsmall hτ hcut

/-- The selected widths. With `N' = N-u`, `K' = M+4u`, `z' = z_live-u`, the
residual free width is unchanged, `N' - z' = N - z_live`, and the physical radius is
`2(N'+V) - K' = 2F - M - 6u`. -/
theorem selection_widths (N V M zl u : ℝ) :
    (N-u) - (zl-u) = N - zl ∧ 2*((N-u)+V) - (M+4*u) = 2*(N+V) - M - 6*u := by
  constructor <;> ring

/-- Prefactor `K' - N' - V = M - F + 5u` plus the child budget `H_phys + u` is `F`. -/
theorem child_exponent_identity (N V M u : ℝ) :
    ((M+4*u) - (N-u) - V) + ((2*((N-u)+V) - (M+4*u)) + u) = N+V := by ring

/-- The physical radius of the child is at least `m - 6u - 2η - τ`. -/
theorem child_radius_lower (m F M u η τ : ℝ) (hM : M ≤ 2*F - m + 2*η + τ) :
    m - 6*u - 2*η - τ ≤ 2*F - M - 6*u := by linarith

/-- The direct diagonal `Z^(K'+ε)` fits `Z^F` when `F + 4u < m` (with the `O(η)` row slack). -/
theorem diagonal_fits (m F M u η τ : ℝ) (hM : M ≤ 2*F - m + 2*η + τ)
    (hgate : F + 4*u + 2*η + τ ≤ m) : M + 4*u ≤ F := by linarith

end
end Qrh.MarkedAnchor.Inverse

#print axioms Qrh.MarkedAnchor.Inverse.initial_geometry
#print axioms Qrh.MarkedAnchor.Inverse.live_initial_margins
