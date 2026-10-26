import Submissions.arvi_repeated_marks_20261024.Faceless.ScalarCert

/-!
# Validity of every step of a piece

`Piece.valid`: from the polynomial certificates of a piece (field guards, the 16 scalar gates, the
weak guard, the special sectors and the cell condition at both width endpoints, and the HIGH gate
for the six branches at both width endpoints), every step `P.node (y - Dy) → P.node y` with
`y ∈ [0, 1]` satisfies `SourceValid2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite Poly

namespace Piece
variable (P : Piece)

/-- The two width endpoints: the crossing `s(y)` and the cap. -/
def endP (e : Fin 2) : Poly := ![P.sp, [capF]] e

/-- The field guards: `B > 0`, `1 - B > 0`, `L - 1 > 0`, `q ≥ 1/2`, `q < 3/4`, `L₀ - L > 0`,
`B₀ ≥ 22/23`, `1 - B₀ > 0`, `L₀ - 1 > 0`. -/
def fieldP : Fin 9 → Poly :=
  ![P.Bp, sub [1] P.Bp, sub P.Lp [1], sub (smul (1 - den) P.L0p) (smul 3 P.B0p),
    sub (smul (9/2) P.B0p) (smul (1 - den) P.L0p), sub P.L0p P.Lp, sub P.B0p [22/23],
    sub [1] P.B0p, sub P.L0p [1]]

/-- The certificates of a piece. -/
structure Certs : Prop where
  sig0 : 0 ≤ P.sig
  H0 : 0 < P.H
  Dy0 : 0 < P.Dy
  capS : P.sig + P.H ≤ capF
  field : ∀ i, ∃ l, pos1I (P.fieldP i) l = true
  scal : ∀ e j, ∃ l, pos1I (P.sgN (P.endP e) j) l = true
  weak : ∀ e, ∃ l, pos1I (P.weakN (P.endP e)) l = true
  sec : ∀ e (j : Fin 3) i, ∃ l, pos1I (P.secB (P.endP e) (j.val + 6) i) l = true
  cell : ∀ e, ∃ l, pos1I (P.cellN (P.endP e)) l = true
  high : ∀ e k, ∃ T, certI (P.highU (P.endP e) k) T = true

variable {P}

theorem Certs.pos {p : Poly} (h : ∃ l, pos1I p l = true) {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < eval p y := by
  obtain ⟨l, hl⟩ := h; exact pos1I_sound p l hl y hy0 hy1

theorem Certs.fieldPos (C : P.Certs) {y : ℚ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < P.B y ∧ P.B y < 1 ∧ 1 < P.L y ∧ 3 * P.B (y - P.Dy) ≤ (1 - den) * P.L (y - P.Dy) ∧
    (1 - den) * P.L (y - P.Dy) < 9/2 * P.B (y - P.Dy) ∧ P.L y < P.L (y - P.Dy) ∧
    22/23 < P.B (y - P.Dy) ∧ P.B (y - P.Dy) < 1 ∧ 1 < P.L (y - P.Dy) := by
  have f := fun i => Certs.pos (C.field i) hy0 hy1
  have f0 := f 0; have f1 := f 1; have f2 := f 2; have f3 := f 3; have f4 := f 4
  have f5 := f 5; have f6 := f 6; have f7 := f 7; have f8 := f 8
  simp [fieldP] at f0 f1 f2 f3 f4 f5 f6 f7 f8
  refine ⟨f0, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem Certs.valid (C : P.Certs) (y : ℚ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    SourceValid2 (P.node y) (P.node (y - P.Dy)) (some (P.node (y - P.Dy))) := by
  obtain ⟨hB, hB1, hL1, hqh, hq34, hLd, hB0, hB01, hL01⟩ := C.fieldPos hy0 hy1
  have hB0p : 0 < P.B (y - P.Dy) := by linarith
  have hL0p : 0 < P.L (y - P.Dy) := by linarith
  have hB0n : P.B (y - P.Dy) ≠ 0 := hB0p.ne'
  have hL0n : P.L (y - P.Dy) ≠ 0 := hL0p.ne'
  have hHD : P.H * P.Dy ≠ 0 := (mul_pos C.H0 C.Dy0).ne'
  have hcross : crossing (P.node y) (P.node (y - P.Dy)) = P.s y := crossing_eq P y hHD hLd.ne'
  have hDn : 0 < P.DnAt y := by simp only [DnAt, den]; positivity
  have hq : P.q y = (1 - den) * P.L (y - P.Dy) / (6 * P.B (y - P.Dy)) := rfl
  have hq1 : 1/2 ≤ P.q y := by rw [hq, le_div_iff₀ (by positivity)]; linarith
  have hq2 : P.q y < 3/4 := by rw [hq, div_lt_iff₀ (by positivity)]; linarith
  have hs0 : 0 ≤ P.s y := by simp only [s]; have := C.sig0; have := C.H0; positivity
  have hs1 : P.s y ≤ capF := by
    simp only [s]; have := C.capS; have := C.H0; nlinarith
  have hcapF : capF < 1 := by norm_num [capF]
  have hcapF0 : 0 ≤ capF := by norm_num [capF]
  -- endpoint facts
  have hend : ∀ e : Fin 2, eval (P.endP e) y = ![P.s y, capF] e := by
    intro e; fin_cases e <;> simp [endP]
  have hbs : ∀ b ∈ [crossing (P.node y) (P.node (y - P.Dy)), (P.node y).cap],
      ∃ e : Fin 2, b = eval (P.endP e) y := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact ⟨0, by rw [hcross, hend]; rfl⟩
    · exact ⟨1, by rw [hend]; rfl⟩
  -- scalar gates
  have hscal : ∀ e : Fin 2, ∀ j, 0 < scalarGate (P.node y) (P.node (y - P.Dy)) (eval (P.endP e) y) j := by
    intro e j
    have hp := Certs.pos (C.scal e j) hy0 hy1
    rw [eval_sgN, ← sgAt_mul _ _ _ _ _ _ hDn.ne' hB0n hL0n, ← scalarGate_at P y _ hB0n hL0n] at hp
    exact pos_of_mul_pos_left hp (by positivity)
  have hweak : ∀ e : Fin 2, 0 < weakCap (P.node y) (P.node (y - P.Dy)) (eval (P.endP e) y) := by
    intro e
    have hp := Certs.pos (C.weak e) hy0 hy1
    rw [eval_weakN, ← weak_mul _ _ _ _ _ hDn.ne' hL0n, ← weakCap_at P y _ hB0n hL0n] at hp
    exact pos_of_mul_pos_left hp (by positivity)
  have hdens : ∀ e : Fin 2, ∀ j : Fin 9, ∀ i : Fin 4, 0 < cubicBernstein
      (fun ν => densityGate2 (P.node y) (P.node (y - P.Dy)) (some (P.node (y - P.Dy)))
        (eval (P.endP e) y) ν j) (P.node y).q (3/4) i := by
    intro e j i
    by_cases hj : j.val < 6
    · have h1 : (fun ν => densityGate2 (P.node y) (P.node (y - P.Dy)) (some (P.node (y - P.Dy)))
          (eval (P.endP e) y) ν j) = fun _ => 1 := by
        funext ν; simp [densityGate2, hj]
      rw [h1]
      fin_cases i <;> norm_num [cubicBernstein, cubicCoeffs]
    · have hj6 : 6 ≤ j.val := by omega
      obtain ⟨j', hj'⟩ : ∃ j' : Fin 3, j'.val + 6 = j.val := ⟨⟨j.val - 6, by omega⟩, by simp; omega⟩
      have hp := Certs.pos (C.sec e j' i) hy0 hy1
      rw [eval_secB] at hp
      have hfun : (fun ν => densityGate2 (P.node y) (P.node (y - P.Dy)) (some (P.node (y - P.Dy)))
          (eval (P.endP e) y) ν j) =
          fun ν => secAt (P.NaAt y (eval (P.endP e) y)) (P.DnAt y) (P.tAt y (eval (P.endP e) y))
            (eval (P.endP e) y) j.val ν := by
        funext ν; exact densityGate_at P y _ ν hB0n hL0n j hj6
      have hsec : ∀ ν, eval (P.secN (P.endP e) (j'.val + 6) ν) y =
          P.DnAt y * secAt (P.NaAt y (eval (P.endP e) y)) (P.DnAt y) (P.tAt y (eval (P.endP e) y))
            (eval (P.endP e) y) j.val ν := by
        intro ν
        rw [eval_secN, hj', ← secAt_mul _ _ _ _ hDn.ne' j.val ν]; ring
      have hcb := cubicBernstein_mul (fun ν => secAt (P.NaAt y (eval (P.endP e) y)) (P.DnAt y)
        (P.tAt y (eval (P.endP e) y)) (eval (P.endP e) y) j.val ν) (P.DnAt y) (eval P.alphaP y)
        (eval P.betaP y) (eval P.sixB0P y) (by simp [sixB0P]; positivity)
        (by simp [betaP, alphaP, sixB0P]; ring) i
      have hqq : (P.node y).q = eval P.alphaP y / eval P.sixB0P y := by
        simp [node, q, alphaP, sixB0P]
      rw [hfun, hqq]
      have hcc : (fun k => cubicCoeffs (fun ν => P.DnAt y * secAt (P.NaAt y (eval (P.endP e) y))
          (P.DnAt y) (P.tAt y (eval (P.endP e) y)) (eval (P.endP e) y) j.val ν) k) =
          fun k => cubic4 (fun ν => eval (P.secN (P.endP e) (j'.val + 6) ν) y) k := by
        funext k; simp only [hsec]; rfl
      rw [hcc] at hcb
      rw [← hcb] at hp
      have hS : 0 < eval P.sixB0P y := by simp [sixB0P]; positivity
      exact pos_of_mul_pos_left hp (by positivity)
  have hcell : ∀ e : Fin 2, 2 * (eval (P.endP e) y - 2 * feeE) ≤
      sourceF (P.node y) (P.node (y - P.Dy)) (eval (P.endP e) y) - feeE := by
    intro e
    have hp := Certs.pos (C.cell e) hy0 hy1
    rw [eval_cellN] at hp
    rw [sourceF_eq P y _ hB0n hL0n]
    have : 0 < ((1 - 6 * (P.NaAt y (eval (P.endP e) y) / P.DnAt y)) - feeE -
        2 * (eval (P.endP e) y - 2 * feeE)) * P.DnAt y := by
      have := hDn.ne'; field_simp; linarith
    have := pos_of_mul_pos_left this hDn.le
    linarith
  -- the HIGH gate at both endpoints, then on the whole cell
  have hhigh : ∀ e : Fin 2, ∀ ν ∈ Set.Icc ((P.q y : ℚ) : ℝ) (3/4), ∀ p ∈ Set.Icc (0:ℝ) (1/2),
      ∀ k, 0 < highGateReal (P.node y) (P.node (y - P.Dy)) (P.node (y - P.Dy)) 8
        ((eval (P.endP e) y : ℚ) : ℝ) ν p k := by
    intro e ν hν p hp k
    obtain ⟨T, hT⟩ := C.high e k
    exact P.high_pos_of_certI (P.endP e) k T hT y hy0 hy1 hB0p hL0p hq2 ν p hν hp
  refine ⟨?_, ?_, hq2, ?_⟩
  · -- SourceValidC
    refine ⟨hB, hB1.le, hL1, hcapF0, hcapF, hq1, hq2.le, hLd, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcross]; exact hs0
    · rw [hcross]; exact hs1
    · rw [hcross]; exact hs1
    · intro h hh
      simp only [Option.mem_def, Option.some.injEq] at hh
      subst hh
      exact ⟨hB0.le, hB01.le, hL01, hcapF0, hcapF⟩
    · intro b hb
      obtain ⟨e, rfl⟩ := hbs b hb
      exact ⟨hscal e, (hweak e).le, hdens e⟩
  · -- HighPos
    intro h hh b hb ν hν p hp k
    simp only [Option.mem_def, Option.some.injEq] at hh
    subst hh
    have h0 := hhigh 0 ν hν p hp k
    have h1 := hhigh 1 ν hν p hp k
    rw [hend] at h0 h1
    have hb' : b ∈ Set.Icc ((P.s y : ℚ) : ℝ) ((capF : ℚ) : ℝ) := by
      rw [hcross] at hb; simpa [node] using hb
    exact width_affine_positive (highGateReal_affine _ _ _ 8 ν p k) hb' (by simpa using h0)
      (by simpa using h1)
  · -- CellRatio
    intro b hb
    obtain ⟨e, rfl⟩ := hbs b hb
    simpa [node] using hcell e

end Piece

end QRH.RepeatedMarks.Faceless
