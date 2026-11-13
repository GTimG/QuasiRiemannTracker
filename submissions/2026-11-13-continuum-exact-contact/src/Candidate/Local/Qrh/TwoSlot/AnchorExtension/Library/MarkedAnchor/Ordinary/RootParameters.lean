/- Modified by Joseph Bebel (2026-11-12) for the 256-stage PR137 extension.
Imports are relocated into the private local fork. Where present, stage and return
parameters instantiate the frozen 0.87334664 extension. Original notices follow.
Pinned upstream: TheSil/QuasiRiemannTracker, 9d81a4c0b0e8338ef458f3ba5139657ae5404fde. -/
/- Copyright (c) 2026 Sil. Apache-2.0.
Root-centering parameters. Mesh precedes N, losses follow the positive
N-dependent gain.
Modified by Sil (2026-10-26): semantic, parametric fork of
`Candidate.FourthPower.RepairedRootParameters`. The face literals (93/25, 3/50,
1 - rootReserve) are replaced by the fields of a `StepData` with `StepGates`; the root
reserve is the chosen reference reserve of `StepGates.reference`; the mesh is also below
the ledger mesh; the width floor is the ledger floor; the lower reference endpoint is
CF (7.1)–(7.2) `(3/2)(P+S+3 u_max-5/6)` with `u_max = sel S + mesh`; the exceptional margin
is stated for a parameter `α < 2/3` (cube-free columns forbid FP's `α ≥ 2/3`).
The N-dependent losses are copied verbatim (over the new mesh, floor and reserve);
`budgetStep` is taken from the cube-free fork `CubeFree.FP.MixedFirstUniformLossBudget`.
The `contrary_inputs` wrapper is not forked (use `IncumbentInput.contrary_inputs`).
Modified by Sil (2026-11-11): fork for the ordinary anchors, namespace
`Qrh.MarkedAnchor.Ordinary.RootParameters`. The centered root exponent is the FIXED reference
width `centeredExponent = D.lref` (`l_ref = 7/50` for the ordinary anchors) in place of the
midpoint of the CF (7.1)–(7.2) interval (empty at the anchor corner); the exceptional parameter
is the fixed `alphaP = D.alpha < 2/3` (`3/5` for the ordinary anchors) in place of `2/3 - ω/2`.
`face_volume` uses the volume gate instead of `1 < L`. The exceptional margin comes from
`StepGates.reference_at`; the native reference gates (`lower`, `upperOne`, `upperTwo`,
`interval_gap`, `reference_gates`, `alphaP_reference_width`) are removed: the reference
rectangle is bounded by the explicit reference-lane hypothesis `ReferenceEnergyFine`
(`FP/RecenteredRootReferenceBound`). -/
import Candidate.Local.Qrh.TwoSlot.AnchorExtension.Library.MarkedAnchor.Ordinary.StepData
import Submissions.sil_density_split_20261026.CubeFree.FP.MixedFirstUniformLossBudget

set_option autoImplicit false
namespace Qrh.MarkedAnchor.Ordinary.RootParameters
open QRH QRH.SilDensitySplit QRH.SilDensitySplit.CubeFree
noncomputable section
open QRH.SilDensitySplit.CubeFree.FP.MixedFirstUniformLossBudget

variable {D : StepData} (G : StepGates D)

/-- Root reserve: half the reference reserve, the child face gap `1-B`, and `1/100`. -/
def rootReserve : ℝ := min (min G.refReserve (1 - D.B)) (1/100) / 2
def mesh (ε:ℝ) : ℝ := min (min (rootReserve G/1024) (ε/1024)) (G.meshL ε)
/-- The large/small split of the live width (the ledger floor). -/
def widthFloor (ε:ℝ) : ℝ := G.floor ε
def mixedReserve : ℝ := rootReserve G/8
def omegaLoss (ε:ℝ) : ℝ := min (rootReserve G/100000) (ε/100000)
def windowLoss (ε:ℝ) : ℝ := min 1 ε/100
def windowCap (N:ℕ)(ε:ℝ) : ℝ := 8+(N:ℝ)*mesh G ε
def seedCap (N:ℕ)(ε:ℝ) : ℝ := 7+(N:ℝ)*mesh G ε
def stepN (N:ℕ)(ε:ℝ) : ℝ :=
  budgetStep (windowCap G N ε) (seedCap G N ε) (windowLoss ε) (mixedReserve G)
def internalScale (N:ℕ)(ε:ℝ) : ℝ :=
  min (stepN G N ε) (min (omegaLoss G ε)
    (min (widthFloor G ε/400) (min (G.tlL ε/100) ((1 - D.Hmin)/100))))
def cutoffLoss (N:ℕ)(ε:ℝ) : ℝ := internalScale G N ε/1000
def artificialLoss (N:ℕ)(ε:ℝ) : ℝ := internalScale G N ε/1000
def massLoss (N:ℕ)(ε:ℝ) : ℝ := internalScale G N ε/1000
def commonPower (N:ℕ)(ε:ℝ) : ℝ := internalScale G N ε/(1000*(seedCap G N ε+1))

theorem rootReserve_spec :
    0 < rootReserve G ∧ 2*rootReserve G ≤ G.refReserve ∧ 2*rootReserve G ≤ 1 - D.B ∧
      rootReserve G ≤ 1/200 := by
  have hρ := G.reference_spec.1
  have hB : D.B < 1 := lt_of_le_of_lt G.face.1 G.face.2.1
  have h1 : min (min G.refReserve (1 - D.B)) (1/100) ≤ min G.refReserve (1 - D.B) :=
    min_le_left _ _
  have h2 : min G.refReserve (1 - D.B) ≤ G.refReserve := min_le_left _ _
  have h3 : min G.refReserve (1 - D.B) ≤ 1 - D.B := min_le_right _ _
  have h4 : min (min G.refReserve (1 - D.B)) (1/100) ≤ 1/100 := min_le_right _ _
  have h0 : 0 < min (min G.refReserve (1 - D.B)) (1/100) :=
    lt_min (lt_min hρ (by linarith)) (by norm_num)
  unfold rootReserve
  refine ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem mesh_spec (ε:ℝ)(hε:0<ε) :
    0<mesh G ε ∧ mesh G ε≤rootReserve G/1024 ∧ mesh G ε≤ε/1024 ∧ mesh G ε ≤ G.meshL ε := by
  have hr := (rootReserve_spec G).1
  have hm := (G.ledger_spec hε).2.2.1
  refine ⟨lt_min (lt_min (by positivity) (by positivity)) hm,
    (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
    min_le_right _ _⟩

theorem widthFloor_spec (ε:ℝ)(hε:0<ε) : 0 < widthFloor G ε ∧ widthFloor G ε ≤ ε/12 := by
  obtain ⟨h0, h1, -⟩ := G.ledger_spec hε
  rw [G.kappa] at h1
  exact ⟨h0, by unfold widthFloor; linarith⟩

theorem omega_spec (ε:ℝ)(hε:0<ε) :
    0<omegaLoss G ε ∧ omegaLoss G ε≤rootReserve G/100000 ∧
      omegaLoss G ε≤ε/100000 ∧ omegaLoss G ε≤1/10000000 := by
  have hr := rootReserve_spec G
  refine ⟨lt_min (by linarith [hr.1]) (by positivity),min_le_left _ _,min_le_right _ _,?_⟩
  exact (min_le_left _ _).trans (by linarith [hr.2.2.2])

theorem cap_spec (N:ℕ)(ε:ℝ)(hε:0<ε) :
    1≤windowCap G N ε ∧ 0≤seedCap G N ε ∧ 0<windowLoss ε ∧ 0<mixedReserve G := by
  have hprod:=mul_nonneg (Nat.cast_nonneg N) (mesh_spec G ε hε).1.le
  refine ⟨?_,?_,div_pos (lt_min zero_lt_one hε) (by norm_num),
    by unfold mixedReserve; linarith [(rootReserve_spec G).1]⟩
  · dsimp only [windowCap];linarith
  · dsimp only [seedCap];linarith

theorem step_pos (N:ℕ)(ε:ℝ)(hε:0<ε) : 0<stepN G N ε := by
  have h:=cap_spec G N ε hε
  exact budget_step_pos _ _ _ _ h.1 h.2.1 h.2.2.1 h.2.2.2

theorem internal_spec (N:ℕ)(ε:ℝ)(hε:0<ε) :
    0 < internalScale G N ε ∧ internalScale G N ε≤stepN G N ε ∧
      internalScale G N ε≤omegaLoss G ε ∧ internalScale G N ε≤widthFloor G ε/400 := by
  refine ⟨lt_min (step_pos G N ε hε) (lt_min (omega_spec G ε hε).1 (lt_min (by
    exact div_pos (widthFloor_spec G ε hε).1 (by norm_num))
      (lt_min (div_pos (G.ledger_spec hε).2.2.2.1 (by norm_num))
        (div_pos (sub_pos.2 G.envelope.2.1) (by norm_num))))),min_le_left _ _,?_,?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

/-- The internal scale is below the ledger frequency tolerance, so the cutoff loss
(entering the defect lower end as `(3/2)·cutoffLoss`) is absorbed by `tl`. -/
theorem internal_le_tl (N:ℕ)(ε:ℝ) : internalScale G N ε ≤ G.tlL ε/100 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))

/-- The internal scale is below the envelope gap `1 - Hmin` (small branch). -/
theorem internal_le_hmin (N:ℕ)(ε:ℝ) : internalScale G N ε ≤ (1 - D.Hmin)/100 :=
  (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))

theorem cutoffLoss_le_hmin (N:ℕ)(ε:ℝ) : 2*cutoffLoss G N ε ≤ 1 - D.Hmin := by
  have h := internal_le_hmin G N ε
  have := G.envelope.2.1
  unfold cutoffLoss; linarith

theorem cutoffLoss_le_tl (N:ℕ)(ε:ℝ)(hε:0<ε) : cutoffLoss G N ε ≤ G.tlL ε/100000 := by
  have h := internal_le_tl G N ε
  unfold cutoffLoss; linarith

theorem cutoffLoss_le_tl' (N:ℕ)(ε:ℝ)(hε:0<ε) : (3/2)*cutoffLoss G N ε ≤ G.tlL ε/100 := by
  have h := cutoffLoss_le_tl G N ε hε
  have := (G.ledger_spec hε).2.2.2.1
  linarith

/-- The combined error fits the actual N-dependent gain; no reverse
comparison between the source mesh and that gain is assumed. -/
theorem internal_losses_paid (N:ℕ)(ε:ℝ)(hε:0<ε) :
    0<cutoffLoss G N ε ∧ 0<artificialLoss G N ε ∧ 0<massLoss G N ε ∧ 0<commonPower G N ε ∧
    4*cutoffLoss G N ε+artificialLoss G N ε+2*seedCap G N ε*commonPower G N ε+massLoss G N ε≤
      min (stepN G N ε/4) (min (omegaLoss G ε/4) ((widthFloor G ε/400)/4)) := by
  have hs:=internal_spec G N ε hε
  have hs0 : 0 < internalScale G N ε := hs.1
  have hB:0≤seedCap G N ε:=(cap_spec G N ε hε).2.1
  have hp:0<commonPower G N ε:=by unfold commonPower;positivity
  have he:commonPower G N ε*(1000*(seedCap G N ε+1))=internalScale G N ε:=by
    unfold commonPower
    exact div_mul_cancel₀ _ (by positivity)
  have hc:2*seedCap G N ε*commonPower G N ε ≤ internalScale G N ε/500:=by nlinarith
  refine ⟨by unfold cutoffLoss;positivity,by unfold artificialLoss;positivity,
    by unfold massLoss;positivity,hp,?_⟩
  apply le_min
  · dsimp only [cutoffLoss,artificialLoss,massLoss];linarith [hs.2.1]
  · apply le_min
    · dsimp only [cutoffLoss,artificialLoss,massLoss];linarith [hs.2.2.1]
    · dsimp only [cutoffLoss,artificialLoss,massLoss];linarith [hs.2.2.2]

theorem original_reserve_paid (N:ℕ)(ε:ℝ)(hε:0<ε) :
    mixedReserve G+4*mesh G ε+4*cutoffLoss G N ε≤rootReserve G := by
  have hm:mesh G ε≤rootReserve G/1024:=(mesh_spec G ε hε).2.1
  have ho:omegaLoss G ε≤rootReserve G/100000:=(omega_spec G ε hε).2.1
  have hs:internalScale G N ε≤omegaLoss G ε:=(internal_spec G N ε hε).2.2.1
  have hr := (rootReserve_spec G).1
  dsimp only [mixedReserve,cutoffLoss]
  linarith

/-- The child root face `P + L S ≤ B`, `s₀ ≤ S ≤ c` (roots below `s₀` are inherited). -/
def Face (P S:ℝ) : Prop := D.s₀≤S ∧ S≤D.c ∧ P+D.L*S≤D.B
/-- Largest selected width at original marked width `S`: `sel S + mesh` (DS §4). -/
def uMax (ε S:ℝ) : ℝ := D.sel ε S+mesh G ε
/-- High branch `A + 3 u_max > 5/6` (with the usual overlapping buffer). -/
def NeedsCentering (ε P S:ℝ) : Prop := 5/6-10*omegaLoss G ε<P+S+3*uMax G ε S
/-- The fixed reference exponent `l_ref`, independent of the root. -/
def centeredExponent (_G : StepGates D) (_ε _P _S:ℝ) : ℝ := D.lref

include G

theorem face_nonneg {P S:ℝ}(h:Face (D:=D) P S) : 0≤S := G.crossing.1.trans h.1

theorem face_volume {P S:ℝ}(h:Face (D:=D) P S) : P+S≤1-rootReserve G := by
  have hS := face_nonneg (G:=G) h
  have hr := (rootReserve_spec G)
  rcases h with ⟨-,hSc,hface⟩
  have hv := G.volume hS hSc
  nlinarith

theorem sel_bounds {ε P S:ℝ}(hε:0<ε)(h:Face (D:=D) P S) :
    0 ≤ D.sel ε S ∧ D.sel ε S ≤ S :=
  (G.sel_spec ε hε).2 S (face_nonneg (G:=G) h) h.2.1

/-- Every actual side selection `u ≤ sel w + m` with `w ≤ S` and `m ≤ mesh` is below
`u_max` (monotone selection). -/
theorem selection_le_uMax {ε w S u m:ℝ}(hε:0<ε)(hw:0≤w)(hwS:w≤S)(hS:S≤D.c)
    (hu:u≤D.sel ε w+m)(hm:m≤mesh G ε) : u≤uMax G ε S := by
  have hmono := (G.sel_spec ε hε).1
  have : D.sel ε w ≤ D.sel ε S :=
    hmono ⟨hw, hwS.trans hS⟩ ⟨hw.trans hwS, hS⟩ hwS
  unfold uMax; linarith

/-- A high root has ordinary width at least `Pref` (high-root threshold of `ReferenceAt`). -/
theorem high_ordinary {ε P S:ℝ}(hε:0<ε)(h:Face (D:=D) P S)(hhigh:NeedsCentering G ε P S) :
    D.Pref≤P := by
  obtain ⟨hs0,hSc,-⟩ := h
  obtain ⟨-,h2,-⟩ := G.reference_at hε hs0 hSc
  have hr := rootReserve_spec G
  have hm := (mesh_spec G ε hε).2.1
  have ho := (omega_spec G ε hε).2.1
  have hm0 := (mesh_spec G ε hε).1
  dsimp only [NeedsCentering,uMax] at hhigh
  linarith

/-- The fixed reference exponent on a high root: `0 < l_ref < P/2 < 1`. -/
theorem centered_spec {ε P S:ℝ}(hε:0<ε)(h:Face (D:=D) P S)(hhigh:NeedsCentering G ε P S) :
    0<centeredExponent G ε P S ∧ centeredExponent G ε P S<P/2 ∧
      centeredExponent G ε P S<1 := by
  have hP := high_ordinary G hε h hhigh
  have hv := face_volume (G:=G) h
  have hS := face_nonneg (G:=G) h
  have hr := (rootReserve_spec G).1
  obtain ⟨-,hl,hlP,-⟩ := G.reference_spec
  dsimp only [centeredExponent]
  refine ⟨hl,by linarith,by linarith⟩

/-- The exceptional parameter: the fixed `alpha < 2/3` of the step data (`3/5` for the ordinary
anchors). -/
def alphaP (_G : StepGates D) (_ε:ℝ) : ℝ := D.alpha

theorem alphaP_spec (ε:ℝ) : alphaP G ε<2/3 ∧ 0<alphaP G ε := by
  obtain ⟨-,-,-,h0,h1,-⟩ := G.reference_spec
  exact ⟨h1,h0⟩

/-- The exceptional margin at the root: with the fixed reference `l_ref` and `alpha`, the principal excess
`A - 5/6 + 3 u_max - alpha·l_ref` is at most `-9ω` (no centering condition is needed). -/
theorem centered_exceptional_margin {ε P S:ℝ}(hε:0<ε)(h:Face (D:=D) P S) :
    P+S+3*uMax G ε S-5/6-alphaP G ε*centeredExponent G ε P S≤-9*omegaLoss G ε := by
  obtain ⟨hs0,hSc,hface⟩ := h
  obtain ⟨h1,-,-⟩ := G.reference_at hε hs0 hSc
  have hr := rootReserve_spec G
  have hm := (mesh_spec G ε hε).2.1
  have ho := (omega_spec G ε hε).2.1
  dsimp only [uMax,alphaP,centeredExponent]
  nlinarith

theorem low_exceptional_margin {ε P S:ℝ}(h:¬NeedsCentering G ε P S) :
    P+S+3*uMax G ε S-5/6≤-10*omegaLoss G ε := by
  have he: P+S+3*uMax G ε S≤5/6-10*omegaLoss G ε:=le_of_not_gt h
  linarith

end
end Qrh.MarkedAnchor.Ordinary.RootParameters
