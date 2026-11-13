/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Scalar data and gates of one generic cube-free common-divisor step
G(B₀,L₀,c₀) → G(B,L,c) (CF §6–7, DS §4–5).

`SideGeometry` is the scalar geometry of one first-common side after selection
(CF §6): original marked width `S`, frozen marked width `f`, extracted common norm
width `cg ≥ f`, side ordinary width `PC` (the root ordinary width is `PC + cg - f`),
selected width `u`, retained marked width `s`, and the frequency defect `t = K₀ - K`.
The packed envelope is `H = 1 + t - 6u` (CF (6.1)) and the live width is `w = S - f`.

`StepGates.ledger` is CF (6.2)–(6.3): the leaf price at the side is paid by the selected
width, `price ≤ u + ε/16`, for every live width above the small-branch floor.
`StepGates.reference` collects the fixed root-reference/diagonal reserves of CF §7 and
DS §5 at `u_max = sel S` (the mesh is paid in `RootParameters`).

Remarks on the gates (shared with the native and density steps of sil-density-split):
* `face`: no `c ≤ c₀` — false for native steps (`face1 → face2` has `c = .067 > c₀ = .06`)
  and never used: the retained cap is the separate inequality `s ≤ c₀ H`. It contains `c < 1/6`.
* `crossing`: the inheritance condition is `(L₀-L) s₀ ≤ B₀ - B`.
  Roots with `S < s₀` satisfy `P + L₀ S ≤ B + (L₀-L) s₀ ≤ B₀`.
  `s₀ ≤ c₀` is only needed when that branch is nonempty, i.e. when `0 < s₀`; natively
  `s₀ = 0` and `c₀ > 0` is not a consequence of `NativeGates` when `a ≥ 1`.
* `SideGeometry.hS` is closed (`s₀ ≤ S`), so the native step (`s₀ = 0`) covers `S = 0`
  and the density step covers `v = 0`, where `HybridGates` is certified.
* `sel_spec` is stated on `[0,c]` (`sel ≤ w` is false for `w < 0`).
* the ledger does not assert `sel w + mesh ≤ w`: greedy selection only needs `sel w ≤ w`
  (in `sel_spec`), and the conjunct fails natively when `a ≥ 1`.
* the small branch is controlled by `envelope.Hmin < 1` and the lemma
  `StepGates.small_envelope`; the small branch (`w < floor`, `u = 0`, native price) does not use `D.sel`, so it does
  not fit `SideGeometry D`.
* native selection fraction is `min a 1`: `NativeGates` allows `a ≥ 1` (large `L`), where
  one selects the whole live block, `s = 0` and the parent price vanishes.
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary`. `StepData` carries the reference parameters `lref`, `alpha` and the
high-root threshold `Pref` (for the ordinary anchors `l_ref = 7/50`, `α = 3/5`). `StepGates.face`
has `0 ≤ L` in place of `1 < L` (the anchors have `L = 0`); `ReferenceAt` consists of the gates
the fork consumes: the volume gate (in place of `1 < L` in `face_volume`), the exceptional
margin at `u_max = sel S`, the high-root threshold `Pref` (so the reference lane only sees roots
with `P ≥ Pref`), and the second-diagonal clause. The native centered-reference-interval
clauses (the interval is empty at the anchor corner `P + 2S > 1`) are dropped. The native
instance is not forked. -/
import Submissions.sil_density_split_20261026.CubeFree.Price
import Submissions.sil_density_split_20261026.Source.NativeBootstrap
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Interval.Set.Basic

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
noncomputable section

/-- Scalar data of a generic cube-free step. `sel ε w` is the target selected width at
live width `w`; `s₀` the crossing width below which roots are inherited. -/
structure StepData where
  B₀ : ℝ
  L₀ : ℝ
  c₀ : ℝ
  B : ℝ
  L : ℝ
  c : ℝ
  κ : ℝ
  s₀ : ℝ
  Hmin : ℝ
  Hmax : ℝ
  sel : ℝ → ℝ → ℝ
  price : Price
  /-- the fixed reference width `l_ref` (`7/50` for the ordinary anchors) -/
  lref : ℝ
  /-- the exceptional saving parameter `α < 2/3` (`3/5` for the ordinary anchors) -/
  alpha : ℝ
  /-- the ordinary-width threshold above which the reference lane is invoked -/
  Pref : ℝ

/-- Scalar geometry of one first-common side (CF §6). -/
structure SideGeometry (D : StepData) (ε mesh tl : ℝ) where
  S : ℝ
  f : ℝ
  cg : ℝ
  PC : ℝ
  u : ℝ
  s : ℝ
  t : ℝ
  hS : D.s₀ ≤ S ∧ S ≤ D.c
  hf : 0 ≤ f ∧ f ≤ cg
  hPC : 0 ≤ PC
  /-- the child root face, with root ordinary width `PC + (cg - f)`, up to the same
  `o(1)` tolerance `tl` as the frequency defect (subunit plain lengths, `ℓ(X) ≠ log_Z X`) -/
  hroot : PC + (cg - f) + D.L*S ≤ D.B + tl
  /-- greedy selection: one upward mesh error -/
  hsel : D.sel ε (S - f) ≤ u ∧ u ≤ D.sel ε (S - f) + mesh
  hs : 0 ≤ s ∧ s ≤ S - f - u
  /-- `K ≥ K₀ - o(1)`; `H ≤ 2 + o(1)` from `V_C ∣ C²`, `A ≤ 1` -/
  ht : -tl ≤ t ∧ t ≤ 1 + 6*u + tl

namespace SideGeometry
variable {D : StepData} {ε mesh tl : ℝ}
/-- Live marked width. -/
def w (g : SideGeometry D ε mesh tl) : ℝ := g.S - g.f
/-- Packed envelope `H = 2a - k + q_C = 1 + t - 6u` (CF (6.1)). -/
def H (g : SideGeometry D ε mesh tl) : ℝ := 1 + g.t - 6*g.u
end SideGeometry

/-- The ledger at a fixed loss `ε` with chosen floor, mesh and frequency tolerances. -/
def LedgerAt (D : StepData) (ε floor meshL tlL : ℝ) : Prop :=
  0 < floor ∧ floor ≤ ε/(16*D.κ) ∧ 0 < meshL ∧ 0 < tlL ∧
  ∀ mesh, 0 ≤ mesh → mesh ≤ meshL → ∀ tl, 0 ≤ tl → tl ≤ tlL →
  ∀ g : SideGeometry D ε mesh tl, floor ≤ g.w →
    D.Hmin ≤ g.H ∧ g.H ≤ D.Hmax ∧ D.price.f g.w g.PC g.s g.H ≤ g.u + ε/16

/-- The fixed root-reference and second-diagonal reserves of the fork, at `u_max = sel S`
(the mesh and the small losses are paid in `RootParameters`):
* parameters: `0 < lref`, `2 lref < Pref`, `0 < alpha < 2/3`;
* volume: `B + (1-L) S ≤ 1 - ρ` on `[0,c]` (stated at the endpoints `S = 0`, `S = c`);
* for `S ∈ [s₀,c]`:
  - the exceptional margin at the worst root `P = B - L S`:
    `P + S + 3 sel S - 5/6 - alpha·lref ≤ -ρ`;
  - high-root threshold: `Pref + S + 3 sel S ≤ 5/6 - ρ` (a root with `A + 3u_max > 5/6 - 10ω`
    has `P ≥ Pref`);
  - second diagonal: `ρ ≤ (1-B) + (L-1) S - 4 sel S`. -/
def ReferenceAt (D : StepData) (ρ : ℝ) : Prop :=
  0 < ρ ∧ 0 < D.lref ∧ 2*D.lref < D.Pref ∧ 0 < D.alpha ∧ D.alpha < 2/3 ∧
  ρ ≤ 1 - D.B ∧ ρ ≤ 1 - D.B - (1 - D.L)*D.c ∧
  ∀ ε > 0, ∀ S, D.s₀ ≤ S → S ≤ D.c →
    ρ ≤ 5/6 + D.alpha*D.lref - D.B - (1 - D.L)*S - 3*D.sel ε S ∧
    ρ ≤ 5/6 - D.Pref - S - 3*D.sel ε S ∧
    ρ ≤ (1-D.B) + (D.L-1)*S - 4*D.sel ε S

/-- The scalar gates of a generic cube-free step. -/
structure StepGates (D : StepData) : Prop where
  face : D.B ≤ D.B₀ ∧ D.B₀ < 1 ∧ D.L < D.L₀ ∧ 0 ≤ D.L ∧ 0 < D.c ∧ D.c < 1/6 ∧ D.c₀ < 1/6
  kappa : D.κ = 3/4
  crossing : 0 ≤ D.s₀ ∧ (D.L₀ - D.L)*D.s₀ ≤ D.B₀ - D.B ∧ (0 < D.s₀ → D.s₀ ≤ D.c₀)
  envelope : 0 < D.Hmin ∧ D.Hmin < 1 ∧ 3 ≤ D.Hmax
  sel_spec : ∀ ε > 0, MonotoneOn (D.sel ε) (Set.Icc 0 D.c) ∧
    ∀ w, 0 ≤ w → w ≤ D.c → 0 ≤ D.sel ε w ∧ D.sel ε w ≤ w
  ledger : ∀ ε > 0, ∃ p : ℝ × ℝ × ℝ, LedgerAt D ε p.1 p.2.1 p.2.2
  reference : ∃ ρ, ReferenceAt D ρ

namespace StepGates
variable {D : StepData}

/-- Chosen ledger parameters `(floor, meshL, tlL)` at loss `ε`. -/
def ledgerParams (G : StepGates D) (ε : ℝ) : ℝ × ℝ × ℝ :=
  if h : 0 < ε then Classical.choose (G.ledger ε h) else (1, 1, 1)

/-- The small-branch floor. -/
def floor (G : StepGates D) (ε : ℝ) : ℝ := (G.ledgerParams ε).1
/-- The largest mesh admitted by the ledger. -/
def meshL (G : StepGates D) (ε : ℝ) : ℝ := (G.ledgerParams ε).2.1
/-- The largest frequency tolerance admitted by the ledger. -/
def tlL (G : StepGates D) (ε : ℝ) : ℝ := (G.ledgerParams ε).2.2

theorem ledger_spec (G : StepGates D) {ε : ℝ} (hε : 0 < ε) :
    LedgerAt D ε (G.floor ε) (G.meshL ε) (G.tlL ε) := by
  have h := Classical.choose_spec (G.ledger ε hε)
  have e : G.ledgerParams ε = Classical.choose (G.ledger ε hε) := by
    unfold ledgerParams; simp [hε]
  simp only [floor, meshL, tlL, e]
  exact h

/-- The chosen reference reserve. -/
def refReserve (G : StepGates D) : ℝ := Classical.choose G.reference

theorem reference_spec (G : StepGates D) : ReferenceAt D G.refReserve :=
  Classical.choose_spec G.reference

/-- The volume gate on the whole width range: `B + (1-L) S ≤ 1 - ρ` for `S ∈ [0,c]`. -/
theorem volume (G : StepGates D) {S : ℝ} (hS0 : 0 ≤ S) (hSc : S ≤ D.c) :
    D.B + (1 - D.L)*S ≤ 1 - G.refReserve := by
  obtain ⟨-, -, -, -, -, h0, hc, -⟩ := G.reference_spec
  rcases le_total 0 (1 - D.L) with h | h
  · have := mul_le_mul_of_nonneg_left hSc h; linarith
  · have := mul_nonpos_of_nonpos_of_nonneg h hS0; linarith

/-- The reference clauses at one width `S ∈ [s₀,c]`. -/
theorem reference_at (G : StepGates D) {ε S : ℝ} (hε : 0 < ε) (hs0 : D.s₀ ≤ S) (hSc : S ≤ D.c) :
    G.refReserve ≤ 5/6 + D.alpha*D.lref - D.B - (1 - D.L)*S - 3*D.sel ε S ∧
    G.refReserve ≤ 5/6 - D.Pref - S - 3*D.sel ε S ∧
    G.refReserve ≤ (1-D.B) + (D.L-1)*S - 4*D.sel ε S :=
  G.reference_spec.2.2.2.2.2.2.2 ε hε S hs0 hSc

/-- The small branch (`u = 0`, native price, CF §6 last paragraph): the envelope
`H = 1 + t` lies in `[Hmin, Hmax]` once `tl ≤ 1 - Hmin`. -/
theorem small_envelope (G : StepGates D) {t tl : ℝ} (htl : tl ≤ 1 - D.Hmin)
    (ht : -tl ≤ t ∧ t ≤ 1 + tl) :
    D.Hmin ≤ 1 + t ∧ 1 + t ≤ D.Hmax := by
  have := G.envelope
  constructor <;> linarith [ht.1, ht.2]

/-- Small-branch native price: below the floor the native cost is at most `ε/16`. -/
theorem small_price (G : StepGates D) {ε s : ℝ} (hε : 0 < ε) (hs : s ≤ G.floor ε) :
    (3/4:ℝ) * max 0 s ≤ ε/16 := by
  obtain ⟨hf0, hf, -⟩ := G.ledger_spec hε
  rw [G.kappa] at hf
  have : max 0 s ≤ ε/12 := max_le (by positivity) (by linarith)
  linarith

/-- Inheritance below the crossing: a root of the child face with `S < s₀` lies in
the parent face. -/
theorem inherit (G : StepGates D) {P S : ℝ} (hS0 : 0 ≤ S) (hS : S < D.s₀)
    (hroot : P + D.L*S ≤ D.B) : P + D.L₀*S ≤ D.B₀ ∧ S ≤ D.c₀ := by
  obtain ⟨-, -, hL, -⟩ := G.face
  obtain ⟨-, hcr, hc⟩ := G.crossing
  refine ⟨?_, hS.le.trans (hc (hS0.trans_lt hS))⟩
  have : (D.L₀ - D.L)*S ≤ (D.L₀ - D.L)*D.s₀ :=
    mul_le_mul_of_nonneg_left hS.le (by linarith)
  nlinarith

end StepGates

end
end Qrh.MarkedAnchor.Ordinary
