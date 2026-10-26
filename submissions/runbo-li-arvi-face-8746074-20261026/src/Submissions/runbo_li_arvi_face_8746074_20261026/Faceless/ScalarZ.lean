import Submissions.runbo_li_arvi_face_8746074_20261026.Faceless.ScalarCert
import Submissions.runbo_li_arvi_face_8746074_20261026.Faceless.Packed

/-!
# Packed sector certificates

The special-sector certificates (`Piece.secB`, three sectors, four Bernstein coefficients, two width
endpoints per piece) are the heaviest scalar certificates: the kernel computes each polynomial in
`Rat` list arithmetic. As for the HIGH certificates (`Packed.lean`), the formula is mirrored on
packed big numbers (`secNZ`, `secBZ`), the packed result is read back once and compared with
literal integer data `g · cS`, and positivity is checked on the data.
-/

set_option autoImplicit false

namespace QRH.RepeatedMarks.Faceless
open Record1252270103Finite QRH.RepeatedMarks.Finite Poly

/-- `p > 0` on `y ∈ [0, 1]`. -/
def PosOn01 (p : Poly) : Prop := ∀ y : ℚ, 0 ≤ y → y ≤ 1 → 0 < eval p y

namespace Pk

open IPoly

section secz
variable (X Δ eIn : ℕ)

/-- `Piece.secN` on packed polynomials. -/
def secNZ (P : Piece) (b : Poly) (j : ℕ) (ν : ℚ) : PZ :=
  let A := ofPoly X Δ (P.NaP b) eIn
  let D := ofPoly X Δ P.DnP eIn
  let t := ofPoly X Δ (P.tP b) eIn
  let bZ := ofPoly X Δ b eIn
  let NF := sub Δ (smul Δ (1 - feeE) D) (smul Δ 6 A)
  let tt := 15 - 6*ν
  let HD := add Δ (smul Δ tt (sub Δ A (smul Δ ν (mul (add Δ t bZ) D))))
    (smul Δ ν (sub Δ (smul Δ 10 D) (smul Δ 60 A)))
  let bD := mul bZ D
  match j with
  | 6 => add Δ HD (smul Δ tt (sub Δ (sub Δ (smul Δ (ν/2) NF) (smul Δ (1 - ν) bD)) (smul Δ feeF D)))
  | 7 => sub Δ (add Δ HD (smul Δ tt (sub Δ (sub Δ (smul Δ (5/6) NF) (smul Δ (1 - ν) bD))
      (smul Δ feeF D)))) (smul Δ (10*ν) NF)
  | _ => sub Δ (add Δ HD (smul Δ tt (sub Δ (sub Δ (smul Δ (ν/2) (sub Δ NF (smul Δ (1/50) D)))
      (smul Δ (1 - ν) bD)) (smul Δ feeF D)))) (smul Δ (10*ν/50) D)

/-- `Piece.secB` on packed polynomials. -/
def secBZ (P : Piece) (b : Poly) (j : ℕ) (i : Fin 4) : PZ :=
  let c := cubic4Z Δ (fun ν => secNZ X Δ eIn P b j ν)
  let N := ofPoly X Δ P.alphaP eIn
  let β := ofPoly X Δ P.betaP eIn
  let S := ofPoly X Δ P.sixB0P eIn
  let a0 := add Δ (add Δ (mul (c 0) (pow S 3)) (mul (c 1) (mul N (pow S 2))))
    (add Δ (mul (c 2) (mul (pow N 2) S)) (mul (c 3) (pow N 3)))
  let a1 := mul β (add Δ (add Δ (mul (c 1) (pow S 2)) (smul Δ 2 (mul (c 2) (mul N S))))
    (smul Δ 3 (mul (c 3) (pow N 2))))
  let a2 := mul (pow β 2) (add Δ (mul (c 2) S) (smul Δ 3 (mul (c 3) N)))
  let a3 := mul (pow β 3) (c 3)
  ![a0, add Δ a0 (smul Δ (1/3) a1), add Δ (add Δ a0 (smul Δ (2/3) a1)) (smul Δ (1/3) a2),
    add Δ (add Δ a0 a1) (add Δ a2 a3)] i

end secz

section secz_reps
variable {X Δ : ℕ}

theorem rep_secNZ (eIn : ℕ) (P : Piece) (b : Poly) (j : ℕ) (ν : ℚ) :
    Rep X Δ (secNZ X Δ eIn P b j ν) (P.secN b j ν) := by
  have hA : Rep X Δ (ofPoly X Δ (P.NaP b) eIn) (P.NaP b) := rep_ofPoly _ _
  have hD : Rep X Δ (ofPoly X Δ P.DnP eIn) P.DnP := rep_ofPoly _ _
  have ht : Rep X Δ (ofPoly X Δ (P.tP b) eIn) (P.tP b) := rep_ofPoly _ _
  have hb : Rep X Δ (ofPoly X Δ b eIn) b := rep_ofPoly _ _
  have hNF := rep_sub (rep_smul (1 - feeE) hD) (rep_smul 6 hA)
  have hHD := rep_add (rep_smul (15 - 6*ν) (rep_sub hA (rep_smul ν (rep_mul (rep_add ht hb) hD))))
    (rep_smul ν (rep_sub (rep_smul 10 hD) (rep_smul 60 hA)))
  have hbD := rep_mul hb hD
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
  rotate_left 6
  · exact rep_add hHD (rep_smul _ (rep_sub (rep_sub (rep_smul _ hNF) (rep_smul _ hbD))
      (rep_smul _ hD)))
  · exact rep_sub (rep_add hHD (rep_smul _ (rep_sub (rep_sub (rep_smul _ hNF) (rep_smul _ hbD))
      (rep_smul _ hD)))) (rep_smul _ hNF)
  all_goals exact rep_sub (rep_add hHD (rep_smul _ (rep_sub (rep_sub
    (rep_smul _ (rep_sub hNF (rep_smul _ hD))) (rep_smul _ hbD)) (rep_smul _ hD)))) (rep_smul _ hD)

theorem rep_secBZ (eIn : ℕ) (P : Piece) (b : Poly) (j : ℕ) (i : Fin 4) :
    Rep X Δ (secBZ X Δ eIn P b j i) (P.secB b j i) := by
  have hc := rep_cubic4Z (X := X) (Δ := Δ) (fun ν => rep_secNZ eIn P b j ν)
  have hN : Rep X Δ (ofPoly X Δ P.alphaP eIn) P.alphaP := rep_ofPoly _ _
  have hβ : Rep X Δ (ofPoly X Δ P.betaP eIn) P.betaP := rep_ofPoly _ _
  have hS : Rep X Δ (ofPoly X Δ P.sixB0P eIn) P.sixB0P := rep_ofPoly _ _
  have ha0 := rep_add (rep_add (rep_mul (hc 0) (rep_pow hS 3)) (rep_mul (hc 1) (rep_mul hN (rep_pow hS 2))))
    (rep_add (rep_mul (hc 2) (rep_mul (rep_pow hN 2) hS)) (rep_mul (hc 3) (rep_pow hN 3)))
  have ha1 := rep_mul hβ (rep_add (rep_add (rep_mul (hc 1) (rep_pow hS 2))
    (rep_smul 2 (rep_mul (hc 2) (rep_mul hN hS)))) (rep_smul 3 (rep_mul (hc 3) (rep_pow hN 2))))
  have ha2 := rep_mul (rep_pow hβ 2) (rep_add (rep_mul (hc 2) hS) (rep_smul 3 (rep_mul (hc 3) hN)))
  have ha3 := rep_mul (rep_pow hβ 3) (hc 3)
  exact rep_vec4 ha0 (rep_add ha0 (rep_smul _ ha1))
    (rep_add (rep_add ha0 (rep_smul _ ha1)) (rep_smul _ ha2)) (rep_add (rep_add ha0 ha1) (rep_add ha2 ha3)) i

end secz_reps

/-- Phase 1 for one sector coefficient: the packed polynomial, read back at base `X`, is `g` times
the data `cS`. -/
def decS (Δ eIn : ℕ) (P : Piece) (b : Poly) (j : ℕ) (i : Fin 4) (g X : ℕ) (cS : IPoly) : Bool :=
  decide (0 < Δ) && decide (0 < g) && (secBZ X Δ eIn P b j i).ok &&
    decide ((secBZ X Δ eIn P b j i).pos1 < X) && decide ((secBZ X Δ eIn P b j i).neg1 < X) &&
    decide (unpack X (secBZ X Δ eIn P b j i) = IPoly.smul g cS)

/-- Phases 1 and 2: `g · cS = Δ^e · secB`, and `cS` is positive on `[0, 1]`. -/
theorem secPos_of_decS (Δ eIn : ℕ) (P : Piece) (b : Poly) (j : ℕ) (i : Fin 4) (g X : ℕ)
    (cS : IPoly) (l : List (ℕ × ℕ)) (hd : decS Δ eIn P b j i g X cS = true)
    (hp : (!l.isEmpty && IPoly.posOn cS 0 0 l) = true) : PosOn01 (P.secB b j i) := by
  intro y hy0 hy1
  simp only [decS, Bool.and_eq_true, decide_eq_true_eq] at hd
  obtain ⟨⟨⟨⟨⟨hΔ, hg⟩, hok⟩, hp1⟩, hn1⟩, hcS⟩ := hd
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hp
  obtain ⟨hne, hpos⟩ := hp
  have h := IPoly.posOn_sound _ 0 0 l hpos y (by simpa using hy0) hy1
    (by intro h'; rw [h'] at hne; simp at hne)
  have h1 := eval_unpack (rep_secBZ eIn P b j i) hok hp1 hn1 y
  rw [hcS, IPoly.eval_smul] at h1
  have hgq : (0:ℚ) < g := by exact_mod_cast hg
  have hΔq : (0:ℚ) < (Δ:ℚ) ^ (secBZ X Δ eIn P b j i).e := by positivity
  have : 0 < (Δ:ℚ) ^ (secBZ X Δ eIn P b j i).e * eval (P.secB b j i) y := by
    rw [← h1]; exact mul_pos hgq h
  exact pos_of_mul_pos_right this hΔq.le

end Pk

end QRH.RepeatedMarks.Faceless
