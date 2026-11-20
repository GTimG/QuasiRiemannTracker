/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.Physical
import Candidate.C092.Intake.QRH.PhysicalCertificate.Initial

/-!
# Literal paired prices on the original E49 direct boxes

The 91 enlarged rectangles are derived from the actual initial partition. Each
polynomial check is recomputed from the original Q1 price by Physical's proved
coefficient generator. Stored direct margins never enter these checks.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace QRH.Cycle092.Direct
noncomputable section
open QRH.Cycle090 QRH.PhysicalCertificate QRH.Coverage

def pairedBoxes : List Box := [
  ⟨(3/8), (27/64), (7/16), (1995/4096)⟩,
  ⟨(27/64), (15/32), (15/32), (63/128)⟩,
  ⟨(45/128), (3/8), (15/32), (1/2)⟩,
  ⟨(3/8), (863/2048), (1995/4096), (1997/4096)⟩,
  ⟨(3/8), (215/512), (1999/4096), (2001/4096)⟩,
  ⟨(3/8), (429/1024), (1001/2048), (501/1024)⟩,
  ⟨(3/8), (855/2048), (1003/2048), (251/512)⟩,
  ⟨(3/8), (853/2048), (2009/4096), (2011/4096)⟩,
  ⟨(3/8), (851/2048), (503/1024), (1007/2048)⟩,
  ⟨(851/2048), (15/32), (63/128), (2017/4096)⟩,
  ⟨(429/1024), (15/32), (2017/4096), (1009/2048)⟩,
  ⟨(861/2048), (15/32), (1009/2048), (2019/4096)⟩,
  ⟨(3/8), (817/2048), (2033/4096), (2035/4096)⟩,
  ⟨(27/64), (15/32), (2019/4096), (505/1024)⟩,
  ⟨(3/8), (431/1024), (1997/4096), (999/2048)⟩,
  ⟨(3/8), (861/2048), (999/2048), (1999/4096)⟩,
  ⟨(867/2048), (15/32), (505/1024), (2021/4096)⟩,
  ⟨(3/8), (407/1024), (2037/4096), (2039/4096)⟩,
  ⟨(3/8), (859/2048), (2001/4096), (1001/2048)⟩,
  ⟨(869/2048), (15/32), (2021/4096), (1011/2048)⟩,
  ⟨(3/8), (813/2048), (2039/4096), (2041/4096)⟩,
  ⟨(3/8), (857/2048), (501/1024), (2005/4096)⟩,
  ⟨(871/2048), (15/32), (1011/2048), (2023/4096)⟩,
  ⟨(3/8), (107/256), (2005/4096), (1003/2048)⟩,
  ⟨(873/2048), (15/32), (2023/4096), (253/512)⟩,
  ⟨(3/8), (811/2048), (1021/2048), (511/1024)⟩,
  ⟨(3/8), (427/1024), (251/512), (2009/4096)⟩,
  ⟨(875/2048), (15/32), (253/512), (2025/4096)⟩,
  ⟨(3/8), (405/1024), (511/1024), (1023/2048)⟩,
  ⟨(3/8), (213/512), (2011/4096), (503/1024)⟩,
  ⟨(219/512), (15/32), (2025/4096), (1013/2048)⟩,
  ⟨(3/8), (809/2048), (1023/2048), (1/2)⟩,
  ⟨(3/8), (425/1024), (1007/2048), (2015/4096)⟩,
  ⟨(439/1024), (15/32), (1013/2048), (2027/4096)⟩,
  ⟨(3/8), (849/2048), (2015/4096), (63/128)⟩,
  ⟨(55/128), (15/32), (2027/4096), (507/1024)⟩,
  ⟨(881/2048), (15/32), (507/1024), (2029/4096)⟩,
  ⟨(3/8), (845/2048), (63/128), (2017/4096)⟩,
  ⟨(883/2048), (15/32), (2029/4096), (1015/2048)⟩,
  ⟨(221/512), (15/32), (1015/2048), (2031/4096)⟩,
  ⟨(443/1024), (15/32), (2031/4096), (127/256)⟩,
  ⟨(887/2048), (15/32), (127/256), (2033/4096)⟩,
  ⟨(111/256), (15/32), (2033/4096), (1017/2048)⟩,
  ⟨(3/8), (839/2048), (2017/4096), (1009/2048)⟩,
  ⟨(445/1024), (15/32), (1017/2048), (2035/4096)⟩,
  ⟨(891/2048), (15/32), (2035/4096), (509/1024)⟩,
  ⟨(3/8), (209/512), (1009/2048), (2019/4096)⟩,
  ⟨(223/512), (15/32), (509/1024), (2037/4096)⟩,
  ⟨(3/8), (417/1024), (2019/4096), (505/1024)⟩,
  ⟨(447/1024), (15/32), (2037/4096), (1019/2048)⟩,
  ⟨(895/2048), (15/32), (1019/2048), (2039/4096)⟩,
  ⟨(3/8), (13/32), (505/1024), (2021/4096)⟩,
  ⟨(7/16), (15/32), (2039/4096), (255/512)⟩,
  ⟨(897/2048), (15/32), (255/512), (2041/4096)⟩,
  ⟨(3/8), (415/1024), (2021/4096), (1011/2048)⟩,
  ⟨(449/1024), (15/32), (2041/4096), (1021/2048)⟩,
  ⟨(3/8), (829/2048), (1011/2048), (2023/4096)⟩,
  ⟨(899/2048), (15/32), (1021/2048), (2043/4096)⟩,
  ⟨(3/8), (827/2048), (2023/4096), (253/512)⟩,
  ⟨(901/2048), (15/32), (2043/4096), (511/1024)⟩,
  ⟨(3/8), (413/1024), (253/512), (2025/4096)⟩,
  ⟨(451/1024), (15/32), (511/1024), (2045/4096)⟩,
  ⟨(3/8), (825/2048), (2025/4096), (1013/2048)⟩,
  ⟨(903/2048), (15/32), (2045/4096), (1023/2048)⟩,
  ⟨(3/8), (103/256), (1013/2048), (2027/4096)⟩,
  ⟨(113/256), (15/32), (1023/2048), (2047/4096)⟩,
  ⟨(3/8), (823/2048), (2027/4096), (507/1024)⟩,
  ⟨(905/2048), (15/32), (2047/4096), (1/2)⟩,
  ⟨(3/8), (411/1024), (507/1024), (2029/4096)⟩,
  ⟨(3/8), (821/2048), (2029/4096), (1015/2048)⟩,
  ⟨(3/8), (205/512), (1015/2048), (2031/4096)⟩,
  ⟨(3/8), (819/2048), (2031/4096), (127/256)⟩,
  ⟨(3/8), (409/1024), (127/256), (2033/4096)⟩,
  ⟨(3/8), (51/128), (2035/4096), (509/1024)⟩,
  ⟨(3/8), (815/2048), (509/1024), (2037/4096)⟩,
  ⟨(3/8), (203/512), (2041/4096), (1021/2048)⟩,
  ⟨(851/2048), (27/64), (503/1024), (1007/2048)⟩,
  ⟨(853/2048), (27/64), (2009/4096), (2011/4096)⟩,
  ⟨(855/2048), (27/64), (1003/2048), (251/512)⟩,
  ⟨(849/2048), (27/64), (2015/4096), (63/128)⟩,
  ⟨(425/1024), (27/64), (1007/2048), (2015/4096)⟩,
  ⟨(213/512), (27/64), (2011/4096), (503/1024)⟩,
  ⟨(429/1024), (27/64), (1001/2048), (501/1024)⟩,
  ⟨(427/1024), (27/64), (251/512), (2009/4096)⟩,
  ⟨(107/256), (27/64), (2005/4096), (1003/2048)⟩,
  ⟨(215/512), (27/64), (1999/4096), (2001/4096)⟩,
  ⟨(857/2048), (27/64), (501/1024), (2005/4096)⟩,
  ⟨(859/2048), (27/64), (2001/4096), (1001/2048)⟩,
  ⟨(861/2048), (27/64), (999/2048), (1999/4096)⟩,
  ⟨(431/1024), (27/64), (1997/4096), (999/2048)⟩,
  ⟨(863/2048), (27/64), (1995/4096), (1997/4096)⟩
]

theorem pairedBoxes_checked : pairedBoxes.all Physical.exteriorBoxCheck = true := by
  decide +kernel

/-- The expanded actual paired price is paid everywhere in every certified box. -/
theorem certified_paired_top {box : Box} (hm : box ∈ pairedBoxes)
    {h g₀ g₁ : ℝ} {point : Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : box.Contains point)
    (hg₀ : 5805911 / 100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913 / 100000000)
    (hg₁ : 3799809 / 50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981 / 5000000) :
    1 / 125000000 ≤ theta - Physical.price h point.1 point.2 g₀ g₁ h := by
  have hc := List.all_eq_true.mp pairedBoxes_checked box hm
  have hclear := Physical.checked_cleared_bound hc hh hh' hp
  have hshape := hc
  simp only [Physical.exteriorBoxCheck, Bool.and_eq_true, decide_eq_true_eq] at hshape
  rcases hshape.1 with ⟨hd, _, hd', hp0, _, hp'⟩
  have hd0 : (0 : ℝ) ≤ (box.uLo : ℝ) := Rat.cast_nonneg.mpr hd
  have hd1 : (box.uHi : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le.mpr hd' : (box.uHi : ℝ) ≤ ((1/2 : ℚ) : ℝ))
  have hp0 : (0 : ℝ) ≤ (box.vLo : ℝ) := Rat.cast_nonneg.mpr hp0
  have hp1 : (box.vHi : ℝ) ≤ (1 / 2 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_le.mpr hp' : (box.vHi : ℝ) ≤ ((1/2 : ℚ) : ℝ))
  exact Physical.top_price_of_cleared hh hh' (hd0.trans hp.1) (hp.2.1.trans hd1)
    (hp0.trans hp.2.2.1) (hp.2.2.2.trans hp1) hg₀ hg₀' hg₁ hg₁' hclear

/-- A certificate covers the whole literal box attached to a direct terminal. -/
def pairCovered (box : Box) : Bool := pairedBoxes.any fun b => decide (Box.Included box b)

/-- Inspect only the genuine route and box; the stored margin is ignored. -/
def pairedTreeCheck (edge : ℕ) : InitialTree → Bool
  | .direct leaf => if leaf.route == "E49_top" then decide (edge = 3) && pairCovered leaf.box else true
  | .central _ => true
  | .uSplit _ lower upper | .vSplit _ lower upper =>
      pairedTreeCheck edge lower && pairedTreeCheck edge upper

/-- Collection from a recursive checker preserves the literal direct-record identity. -/
theorem pairedTreeCheck_sound (edge : ℕ) (tree : InitialTree)
    (hc : pairedTreeCheck edge tree = true) {leaf : DirectLeaf}
    (hm : leaf ∈ tree.directRecords) (hr : leaf.route = "E49_top") :
    edge = 3 ∧ ∃ box ∈ pairedBoxes, Box.Included leaf.box box := by
  induction tree with
  | direct record =>
      simp only [InitialTree.directRecords, List.mem_singleton] at hm
      subst leaf
      simp only [pairedTreeCheck, hr, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true,
        decide_eq_true_eq] at hc
      refine ⟨hc.1, ?_⟩
      exact List.any_eq_true.mp hc.2 |>.imp fun box h => ⟨h.1, of_decide_eq_true h.2⟩
  | central n => simp [InitialTree.directRecords] at hm
  | uSplit cut lower upper hl hu | vSplit cut lower upper hl hu =>
      simp only [pairedTreeCheck, Bool.and_eq_true] at hc
      simp only [InitialTree.directRecords, List.mem_append] at hm
      rcases hm with hm | hm
      · exact hl hc.1 hm
      · exact hu hc.2 hm

end
end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.pairedBoxes_checked
#print axioms QRH.Cycle092.Direct.certified_paired_top
