import Candidate.Target830.Count.Monotonicity
import Candidate.Uneven.MainCountParameters

/- Original module: Candidate.Uneven.MainCountAvailability. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
set_option maxHeartbeats 0

namespace OAI.SevenEighths.MainCount
noncomputable section
open Target830 Target830.Count

def guardD (P : Plane) (δ p : ℝ) : ℝ := affineD P.lambda p
def guardA (P : Plane) (δ p : ℝ) : ℝ := affineA P.lambda p
def guardC (P : Plane) (δ p : ℝ) : ℝ := affineC P.lambda P.B p
def guardJ (P : Plane) (δ p : ℝ) : ℝ := affineJ P.lambda δ p
def guardTLo (P : Plane) (δ p : ℝ) : ℝ := affineTNum P.lambda P.B δ p-affineJ P.lambda δ p
def guardTHi (P : Plane) (δ p : ℝ) : ℝ :=
  (12499/10000)*affineJ P.lambda δ p-affineTNum P.lambda P.B δ p
def guardRLo (P : Plane) (δ p : ℝ) : ℝ :=
  affineRNum P.lambda P.B δ p-(23/37)*affineD P.lambda p*affineJ P.lambda δ p
def guardRHi (P : Plane) (δ p : ℝ) : ℝ :=
  affineD P.lambda p*affineJ P.lambda δ p-affineRNum P.lambda P.B δ p
def guardMLo (P : Plane) (δ p : ℝ) : ℝ :=
  affineMNum P.lambda P.B δ p-
    max plainLower ((P.B-P.lambda*widthUpper)/2+1/100000)*
      affineD P.lambda p*affineJ P.lambda δ p
def guardMHi (P : Plane) (δ p : ℝ) : ℝ :=
  mHi*affineD P.lambda p*affineJ P.lambda δ p-affineMNum P.lambda P.B δ p
def guardWidth (P : Plane) (δ p : ℝ) : ℝ :=
  ((P.B-P.lambda*(3401/100000))/2-1/100000)*
    affineD P.lambda p*affineJ P.lambda δ p-affineMNum P.lambda P.B δ p
def guardTail (P : Plane) (δ p : ℝ) : ℝ :=
  affineN P.lambda P.B δ p-(1-2*δ*mHi-2*δ*p*widthLower)*affineJ P.lambda δ p
def guardMonotone (P : Plane) (δ p : ℝ) : ℝ := affineAntitone P.lambda P.B δ p

/-- All scalar admissions required before using an affine count. -/
structure Admissible (P : Plane) (δ p : ℝ) : Prop where
  denominator : 0 < guardD P δ p
  a : 0 < guardA P δ p
  c : 0 < guardC P δ p
  j : 0 < guardJ P δ p
  cutoff_lower : 0 < guardTLo P δ p
  cutoff_upper : 0 < guardTHi P δ p
  cross_lower : 0 < guardRLo P δ p
  cross_upper : 0 < guardRHi P δ p
  plain_lower : 0 < guardMLo P δ p
  plain_upper : 0 < guardMHi P δ p
  selected_lower : 0 < guardWidth P δ p
  tail : 0 < guardTail P δ p
  monotone : 0 < guardMonotone P δ p

structure Window where
  plane : Plane
  deltaLo : ℝ
  deltaHi : ℝ
  pLo : ℝ
  bounds : 0 ≤ deltaLo ∧ deltaLo < deltaHi ∧ deltaHi ≤ 3/4 ∧ 0 ≤ pLo ∧ pLo < 1/2

def Window.Available (w : Window) (δ p : ℝ) : Prop :=
  δ ∈ Set.Icc w.deltaLo w.deltaHi ∧ p ∈ Set.Icc w.pLo (1/2)

def Window.toBranch (w : Window)
    (hc : ∀ δ p, w.Available δ p → Admissible w.plane δ p) : Branch where
  available := w.Available
  value := affineR w.plane.lambda w.plane.B
  upward := by
    intro δ p q hp hpq hq
    exact ⟨hp.1,⟨hp.2.1.trans hpq,hq⟩⟩
  antitone := by
    intro δ p q hp hq hpq
    have hδ0 : 0 ≤ δ := w.bounds.1.trans hp.1.1
    have hδhi : δ ≤ 5/6 := by linarith [hp.1.2,w.bounds.2.2.1]
    have hanti := affineR_antitoneOn hδ0 hδhi
      (fun z hz => (hc δ z ⟨hp.1,hz⟩).j)
      (fun z hz => (hc δ z ⟨hp.1,hz⟩).monotone.le)
    exact hanti hp.2 hq.2 hpq

end
end OAI.SevenEighths.MainCount
end

/- Original module: Candidate.Uneven.MainCountWindows. -/
section
/- Adapted from PR63 by Sil with OpenAI Codex assistance. Apache-2.0. -/

set_option autoImplicit false
namespace OAI.SevenEighths.MainCount
noncomputable section

inductive Stage where
  | warmup | final
  deriving DecidableEq

def Stage.aPlane : Stage → Plane | .warmup => .A2 | .final => .A
def Stage.cPlane : Stage → Plane | .warmup => .C2 | .final => .C
def Stage.deltaLo : Stage → ℝ | .warmup => 4543/10000 | .final => 9087/20000

/-- Only the two new estimates valid at the current incumbent are used. -/
def Stage.Supports (S : Stage) (P : Plane) : Prop :=
  P=.PR62 ∨ P=.PR60 ∨ P=.oldA ∨ P=.oldC ∨ P=.oldWeak ∨
    P=S.aPlane ∨ P=S.cPlane


def window10 (S : Stage) : Window where
  plane := S.aPlane
  deltaLo := S.deltaLo
  deltaHi := 117/256
  pLo := 127/256
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window11 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 117/256
  deltaHi := 237/512
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window12 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 237/512
  deltaHi := 15/32
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window13 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 15/32
  deltaHi := 123/256
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

def window14 (S : Stage) : Window where
  plane := S.cPlane
  deltaLo := 123/256
  deltaHi := 63/128
  pLo := 63/128
  bounds := by cases S <;> norm_num [Stage.deltaLo]

end
end OAI.SevenEighths.MainCount
end
