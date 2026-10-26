/- Repeated marks: the source chain as one explicit family of faces, generic part.

The faces are the secant lines of a piecewise-cubic envelope that tracks the closed-form (Lambert)
switching flow of the continuum source chain (`research/chain-ode`, `research/faceless-chain`).
`Faceless.Piece.Certs.valid` proves the source step for every face of a piece at once; a piece is an
induction along its grid `y = i/2^16` (`piece_sources`). The chain itself, from the start face
through every piece, is generated: `Faceless/Gen/Chain.lean`. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Faceless.Validity
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Graph.NaturalCap
import Submissions.hailey_collet_1252270103.Record1252270103Graph.GraphContract
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.RepeatedMarks.Graph
noncomputable section
open Record1252270103Finite OAI.SevenEighths QRH.Record1252270103Graph QRH.RepeatedMarks.Finite
open QRH.RepeatedMarks.Faceless

/-- The source step of the repeated-mark chain: a HIGH parent is always present. -/
def NFStep2 : Prop := ∀ n low h : Source,
 (51/100:ℝ)≤HeckeZeroSupremum.beta → 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK →
 SourceValid2 n low (some h) → ParentGood low → NFAccounting n →
 P low → P h → P n

lemma parent_good_of_valid2 {n low : Source} {h : Option Source}
 (hv : SourceValid2 n low h) : ParentGood n :=
 ⟨hv.1.1,hv.1.2.1,hv.1.2.2.1,hv.1.2.2.2.1,hv.1.2.2.2.2.1⟩

/-- The HIGH parent of a valid step is a good parent. -/
lemma parent_good_of_high {n low h : Source} (hv : SourceValid2 n low (some h)) : ParentGood h := by
  obtain ⟨hB, hB1, hL, hc0, hc1⟩ := hv.1.2.2.2.2.2.2.2.2.2.2.2.1 h (by simp)
  exact ⟨lt_of_lt_of_le (by norm_num) hB, hB1, hL, hc0, hc1⟩

lemma nf_accounting_node (P : Piece) (y : ℚ) : NFAccounting (P.node y) :=
  Or.inr ⟨rfl, rfl, rfl⟩

/-- Every face of a piece on the grid `y = i·Dy` is a global source. -/
theorem piece_sources (step : NFStep2) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hk : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (P : Piece) (C : P.Certs)
    (hD : P.Dy * 2 ^ 16 = 1) (h0 : QRH.Record1252270103Graph.P (P.node 0)) :
    ∀ i : ℕ, i < 2 ^ 16 → QRH.Record1252270103Graph.P (P.node (i * P.Dy)) := by
  intro i
  induction i with
  | zero => intro _; simpa using h0
  | succ i ih =>
    intro hi
    have hD0 := C.Dy0
    have hy0 : 0 ≤ ((i + 1 : ℕ) : ℚ) * P.Dy := by positivity
    have hy1 : ((i + 1 : ℕ) : ℚ) * P.Dy ≤ 1 := by
      have : ((i + 1 : ℕ) : ℚ) ≤ 2 ^ 16 := by exact_mod_cast hi.le
      calc ((i + 1 : ℕ) : ℚ) * P.Dy ≤ 2 ^ 16 * P.Dy := by gcongr
        _ = 1 := by rw [mul_comm]; exact hD
    have hprev : ((i + 1 : ℕ) : ℚ) * P.Dy - P.Dy = (i : ℚ) * P.Dy := by push_cast; ring
    have hv := C.valid _ hy0 hy1
    rw [hprev] at hv
    have hpar := ih (by omega)
    exact step _ _ _ hβ hk hv (parent_good_of_high hv) (nf_accounting_node P _) hpar hpar

/-- The last face of a piece. -/
theorem piece_last (step : NFStep2) (hβ : (51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hk : 6*(2*HeckeZeroSupremum.beta-1)≤QRH.RepeatedMarks.natK) (P : Piece) (C : P.Certs)
    (hD : P.Dy * 2 ^ 16 = 1) (h0 : QRH.Record1252270103Graph.P (P.node 0)) :
    QRH.Record1252270103Graph.P (P.node (1 - P.Dy)) := by
  have h := piece_sources step hβ hk P C hD h0 (2 ^ 16 - 1) (by norm_num)
  have : ((2 ^ 16 - 1 : ℕ) : ℚ) * P.Dy = 1 - P.Dy := by
    push_cast; linear_combination hD
  rwa [this] at h

end
end QRH.RepeatedMarks.Graph
