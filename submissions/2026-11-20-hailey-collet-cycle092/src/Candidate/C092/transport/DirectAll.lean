/- Copyright (c) 2026 Hailey Collet. Apache-2.0. -/
import Candidate.C092.transport.DirectPairAll
import Candidate.C092.transport.DirectCertificates
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace QRH.Cycle092.Direct
open QRH.PhysicalCertificate QRH.Coverage QRH.Cycle090

def certificateCovers (route : CountRoute) (edge : ℕ) (box : Box) : Bool :=
  directCertificates.any fun c => decide
    (c.route=route ∧ c.edge.val=edge ∧ Box.Included box c.box)

def IsCovered (route : CountRoute) (edge : ℕ) (box : Box) : Prop :=
  ∃ c ∈ directCertificates, c.route=route ∧ c.edge.val=edge ∧ Box.Included box c.box

theorem certificateCovers_sound (route : CountRoute) (edge : ℕ) (box : Box)
    (hc : certificateCovers route edge box = true) : IsCovered route edge box := by
  obtain ⟨c,hm,hc⟩ := List.any_eq_true.mp hc
  exact ⟨c,hm,of_decide_eq_true hc⟩

def otherLeafCheck (edge : ℕ) (leaf : DirectLeaf) : Bool :=
  if leaf.route == "E49_top" then true else
  if leaf.route == "original_saved" then certificateCovers .old edge leaf.box else
  if leaf.route == "native_current_exact" then certificateCovers .native edge leaf.box else
  if leaf.route == "fixed_interior_detector" then
    certificateCovers .fixedS edge leaf.box && certificateCovers .fixedA edge leaf.box else false

def otherTreeCheck (edge : ℕ) : InitialTree → Bool
  | .direct leaf => otherLeafCheck edge leaf
  | .central _ => true
  | .uSplit _ a b | .vSplit _ a b => otherTreeCheck edge a && otherTreeCheck edge b

theorem otherTreeCheck_sound (edge : ℕ) (tree : InitialTree)
    (hc : otherTreeCheck edge tree = true) {leaf : DirectLeaf}
    (hm : leaf ∈ tree.directRecords) : otherLeafCheck edge leaf = true := by
  induction tree with
  | direct record =>
      simp only [InitialTree.directRecords,List.mem_singleton] at hm
      subst leaf; exact hc
  | central n => simp [InitialTree.directRecords] at hm
  | uSplit cut a b ha hb | vSplit cut a b ha hb =>
      simp only [otherTreeCheck,Bool.and_eq_true] at hc
      simp only [InitialTree.directRecords,List.mem_append] at hm
      rcases hm with hm | hm
      · exact ha hc.1 hm
      · exact hb hc.2 hm

theorem otherLeafCheck_sound (edge : ℕ) (leaf : DirectLeaf)
    (hc : otherLeafCheck edge leaf = true) :
    leaf.route="E49_top" ∨
    (leaf.route="original_saved" ∧ IsCovered .old edge leaf.box) ∨
    (leaf.route="native_current_exact" ∧ IsCovered .native edge leaf.box) ∨
    (leaf.route="fixed_interior_detector" ∧ IsCovered .fixedS edge leaf.box ∧
      IsCovered .fixedA edge leaf.box) := by
  by_cases h1 : leaf.route="E49_top"
  · exact Or.inl h1
  by_cases h2 : leaf.route="original_saved"
  · exact Or.inr (Or.inl ⟨h2,certificateCovers_sound _ _ _ (by simpa [otherLeafCheck,h1,h2] using hc)⟩)
  by_cases h3 : leaf.route="native_current_exact"
  · exact Or.inr (Or.inr (Or.inl ⟨h3,certificateCovers_sound _ _ _ (by simpa [otherLeafCheck,h1,h2,h3] using hc)⟩))
  by_cases h4 : leaf.route="fixed_interior_detector"
  · have h : certificateCovers .fixedS edge leaf.box = true ∧ certificateCovers .fixedA edge leaf.box = true := by
      simpa [otherLeafCheck,h4] using hc
    exact Or.inr (Or.inr (Or.inr ⟨h4,certificateCovers_sound _ _ _ h.1,certificateCovers_sound _ _ _ h.2⟩))
  · simp [otherLeafCheck,h1,h2,h3,h4] at hc

theorem other_initial00 : otherTreeCheck 0 initialTree00 = true := by
  decide +kernel

theorem other_initial01 : otherTreeCheck 1 initialTree01 = true := by
  decide +kernel

theorem other_initial02 : otherTreeCheck 1 initialTree02 = true := by
  decide +kernel

theorem other_initial03 : otherTreeCheck 2 initialTree03 = true := by
  decide +kernel

theorem other_initial04 : otherTreeCheck 2 initialTree04 = true := by
  decide +kernel

theorem other_initial05 : otherTreeCheck 3 initialTree05 = true := by
  decide +kernel

theorem other_initial06 : otherTreeCheck 3 initialTree06 = true := by
  decide +kernel

theorem other_initial07 : otherTreeCheck 3 initialTree07 = true := by
  decide +kernel

theorem other_initial08 : otherTreeCheck 3 initialTree08 = true := by
  decide +kernel

theorem other_initial09 : otherTreeCheck 3 initialTree09 = true := by
  decide +kernel

theorem other_initial10 : otherTreeCheck 3 initialTree10 = true := by
  decide +kernel

theorem other_initial11 : otherTreeCheck 3 initialTree11 = true := by
  decide +kernel

theorem other_initial12 : otherTreeCheck 3 initialTree12 = true := by
  decide +kernel

theorem other_initial13 : otherTreeCheck 3 initialTree13 = true := by
  decide +kernel

theorem other_initial14 : otherTreeCheck 3 initialTree14 = true := by
  decide +kernel

theorem other_initial15 : otherTreeCheck 3 initialTree15 = true := by
  decide +kernel

theorem other_initial16 : otherTreeCheck 3 initialTree16 = true := by
  decide +kernel

theorem other_initial17 : otherTreeCheck 3 initialTree17 = true := by
  decide +kernel

theorem other_initial18 : otherTreeCheck 3 initialTree18 = true := by
  decide +kernel

theorem other_initial19 : otherTreeCheck 3 initialTree19 = true := by
  decide +kernel

theorem other_initial20 : otherTreeCheck 3 initialTree20 = true := by
  decide +kernel

theorem other_initial21 : otherTreeCheck 3 initialTree21 = true := by
  decide +kernel

theorem other_initial22 : otherTreeCheck 3 initialTree22 = true := by
  decide +kernel

theorem other_initial23 : otherTreeCheck 3 initialTree23 = true := by
  decide +kernel

theorem other_initial24 : otherTreeCheck 3 initialTree24 = true := by
  decide +kernel

theorem other_initial25 : otherTreeCheck 3 initialTree25 = true := by
  decide +kernel

theorem other_initial26 : otherTreeCheck 3 initialTree26 = true := by
  decide +kernel

theorem other_initial27 : otherTreeCheck 3 initialTree27 = true := by
  decide +kernel

theorem other_initial28 : otherTreeCheck 3 initialTree28 = true := by
  decide +kernel

theorem other_initial29 : otherTreeCheck 3 initialTree29 = true := by
  decide +kernel

theorem other_initial30 : otherTreeCheck 3 initialTree30 = true := by
  decide +kernel

theorem other_initial31 : otherTreeCheck 3 initialTree31 = true := by
  decide +kernel

theorem other_initial32 : otherTreeCheck 3 initialTree32 = true := by
  decide +kernel

theorem other_initial33 : otherTreeCheck 3 initialTree33 = true := by
  decide +kernel

theorem other_initial34 : otherTreeCheck 3 initialTree34 = true := by
  decide +kernel

theorem other_initial35 : otherTreeCheck 3 initialTree35 = true := by
  decide +kernel

theorem other_initial36 : otherTreeCheck 3 initialTree36 = true := by
  decide +kernel

theorem other_initial37 : otherTreeCheck 3 initialTree37 = true := by
  decide +kernel

theorem other_initial38 : otherTreeCheck 3 initialTree38 = true := by
  decide +kernel

theorem other_initial39 : otherTreeCheck 3 initialTree39 = true := by
  decide +kernel

theorem other_initial40 : otherTreeCheck 3 initialTree40 = true := by
  decide +kernel

theorem other_initial41 : otherTreeCheck 3 initialTree41 = true := by
  decide +kernel

theorem other_initial42 : otherTreeCheck 3 initialTree42 = true := by
  decide +kernel

theorem other_initial43 : otherTreeCheck 3 initialTree43 = true := by
  decide +kernel

theorem other_initial44 : otherTreeCheck 3 initialTree44 = true := by
  decide +kernel

theorem other_initial45 : otherTreeCheck 3 initialTree45 = true := by
  decide +kernel

theorem other_initial46 : otherTreeCheck 3 initialTree46 = true := by
  decide +kernel

theorem other_initial47 : otherTreeCheck 3 initialTree47 = true := by
  decide +kernel

theorem other_initial48 : otherTreeCheck 3 initialTree48 = true := by
  decide +kernel

theorem other_initial49 : otherTreeCheck 3 initialTree49 = true := by
  decide +kernel

theorem other_initial50 : otherTreeCheck 3 initialTree50 = true := by
  decide +kernel

theorem other_initial51 : otherTreeCheck 3 initialTree51 = true := by
  decide +kernel

theorem other_initial52 : otherTreeCheck 3 initialTree52 = true := by
  decide +kernel

theorem other_initial53 : otherTreeCheck 3 initialTree53 = true := by
  decide +kernel

theorem other_initial54 : otherTreeCheck 3 initialTree54 = true := by
  decide +kernel

theorem other_initial55 : otherTreeCheck 3 initialTree55 = true := by
  decide +kernel

theorem other_initial56 : otherTreeCheck 3 initialTree56 = true := by
  decide +kernel

theorem actual_initial_other_check (index : Fin 57) :
    otherTreeCheck (originalAt index).edge (initialAt index) = true := by
  fin_cases index
  · exact other_initial00
  · exact other_initial01
  · exact other_initial02
  · exact other_initial03
  · exact other_initial04
  · exact other_initial05
  · exact other_initial06
  · exact other_initial07
  · exact other_initial08
  · exact other_initial09
  · exact other_initial10
  · exact other_initial11
  · exact other_initial12
  · exact other_initial13
  · exact other_initial14
  · exact other_initial15
  · exact other_initial16
  · exact other_initial17
  · exact other_initial18
  · exact other_initial19
  · exact other_initial20
  · exact other_initial21
  · exact other_initial22
  · exact other_initial23
  · exact other_initial24
  · exact other_initial25
  · exact other_initial26
  · exact other_initial27
  · exact other_initial28
  · exact other_initial29
  · exact other_initial30
  · exact other_initial31
  · exact other_initial32
  · exact other_initial33
  · exact other_initial34
  · exact other_initial35
  · exact other_initial36
  · exact other_initial37
  · exact other_initial38
  · exact other_initial39
  · exact other_initial40
  · exact other_initial41
  · exact other_initial42
  · exact other_initial43
  · exact other_initial44
  · exact other_initial45
  · exact other_initial46
  · exact other_initial47
  · exact other_initial48
  · exact other_initial49
  · exact other_initial50
  · exact other_initial51
  · exact other_initial52
  · exact other_initial53
  · exact other_initial54
  · exact other_initial55
  · exact other_initial56

noncomputable section
/-- The original physical price selected by each actual direct route. The fixed
route retains both count faces and the original 10^-11 count collar. -/
def directPrice (edge : Fin 4) (leaf : DirectLeaf) (h d p g₀ g₁ : ℝ) : ℝ :=
  if leaf.route="original_saved" then originalPrice .old edge h d p else
  if leaf.route="native_current_exact" then originalPrice .native edge h d p else
  if leaf.route="fixed_interior_detector" then
    max (originalPrice .fixedS edge h d p) (originalPrice .fixedA edge h d p)
  else Physical.price h d p g₀ g₁ h

/-- Every real point of every actual direct box has an original physical route
with positive surplus. No stored margin and no unproved box-price premise occurs. -/
theorem all_actual_direct_prices {index : Fin 57} {leaf : DirectLeaf}
    (hm : leaf ∈ (initialAt index).directRecords)
    {h g₀ g₁ : ℝ} {point : Point}
    (hh : hLower ≤ h) (hh' : h ≤ hUpper) (hp : leaf.box.Contains point)
    (hg₀ : 5805911/100000000 ≤ g₀) (hg₀' : g₀ ≤ 5805913/100000000)
    (hg₁ : 3799809/50000000 ≤ g₁) (hg₁' : g₁ ≤ 379981/5000000) :
    ∃ edge : Fin 4, edge.val=(originalAt index).edge ∧
      1/125000000 ≤ theta-directPrice edge leaf h point.1 point.2 g₀ g₁ := by
  have hc := otherTreeCheck_sound _ _ (actual_initial_other_check index) hm
  rcases otherLeafCheck_sound _ _ hc with hr | ⟨hr,c,hc,hroute,he,hin⟩ |
    ⟨hr,c,hc,hroute,he,hin⟩ | ⟨hr,hs,ha⟩
  · have hpair := all_actual_E49_price hm hr hh hh' hp hg₀ hg₀' hg₁ hg₁'
    exact ⟨3,hpair.1.symm,by simpa [directPrice,hr] using hpair.2⟩
  · have hpaid := certified_original_price hc hh hh' (Box.contains_of_included hin hp)
    rw [hroute] at hpaid
    refine ⟨c.edge,he,?_⟩
    simp only [directPrice,hr,↓reduceIte]
    linarith
  · have hpaid := certified_original_price hc hh hh' (Box.contains_of_included hin hp)
    rw [hroute] at hpaid
    refine ⟨c.edge,he,?_⟩
    simp [directPrice,hr]
    linarith
  · obtain ⟨cs,hcs,hrs,hes,hins⟩ := hs
    obtain ⟨ca,hca,hra,hea,hina⟩ := ha
    have hesame : ca.edge=cs.edge := Fin.ext (hea.trans hes.symm)
    have hpaidS := certified_original_price hcs hh hh' (Box.contains_of_included hins hp)
    have hpaidA := certified_original_price hca hh hh' (Box.contains_of_included hina hp)
    rw [hrs] at hpaidS
    rw [hra,hesame] at hpaidA
    refine ⟨cs.edge,hes,?_⟩
    have hmax : max (originalPrice .fixedS cs.edge h point.1 point.2)
        (originalPrice .fixedA cs.edge h point.1 point.2) ≤ theta-1/125000000 :=
      max_le (by linarith) (by linarith)
    simpa [directPrice,hr] using (show 1/125000000 ≤ theta-
      max (originalPrice .fixedS cs.edge h point.1 point.2)
        (originalPrice .fixedA cs.edge h point.1 point.2) from by linarith)

end
end QRH.Cycle092.Direct
#print axioms QRH.Cycle092.Direct.all_actual_direct_prices
