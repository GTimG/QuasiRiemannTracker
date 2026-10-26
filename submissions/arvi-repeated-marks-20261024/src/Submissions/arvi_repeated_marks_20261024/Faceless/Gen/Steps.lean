import Submissions.arvi_repeated_marks_20261024.Faceless.Gen.Data

set_option autoImplicit false
set_option maxRecDepth 100000

namespace QRH.RepeatedMarks.Faceless

open Record1252270103Finite QRH.RepeatedMarks.Finite

def step0_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def step0_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem step0_validC : SourceValidC (piece0.node 0) (natural) (some (natural)) := by decide +kernel
theorem step0_highL : HighCertAt (piece0.node 0) (natural) (natural) 8 (crossing (piece0.node 0) (natural)) step0_treesL := by
  decide +kernel
theorem step0_highR : HighCertAt (piece0.node 0) (natural) (natural) 8 (piece0.node 0).cap step0_treesR := by
  decide +kernel
theorem step0_q : (piece0.node 0).q < 3/4 := by decide +kernel
theorem step0_cell : CellRatio (piece0.node 0) (natural) := by decide +kernel
theorem step0_valid : SourceValid2 (piece0.node 0) (natural) (some (natural)) := by
  refine ⟨step0_validC, highPos_of_valid _ _ _ _ step0_q ?_, step0_q, step0_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, step0_highL⟩
  · exact ⟨_, step0_highR⟩

def junction1_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction1_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction1_validC : SourceValidC (piece1.node 0) (piece0.node (1 - piece0.Dy)) (some (piece0.node (1 - piece0.Dy))) := by decide +kernel
theorem junction1_highL : HighCertAt (piece1.node 0) (piece0.node (1 - piece0.Dy)) (piece0.node (1 - piece0.Dy)) 8 (crossing (piece1.node 0) (piece0.node (1 - piece0.Dy))) junction1_treesL := by
  decide +kernel
theorem junction1_highR : HighCertAt (piece1.node 0) (piece0.node (1 - piece0.Dy)) (piece0.node (1 - piece0.Dy)) 8 (piece1.node 0).cap junction1_treesR := by
  decide +kernel
theorem junction1_q : (piece1.node 0).q < 3/4 := by decide +kernel
theorem junction1_cell : CellRatio (piece1.node 0) (piece0.node (1 - piece0.Dy)) := by decide +kernel
theorem junction1_valid : SourceValid2 (piece1.node 0) (piece0.node (1 - piece0.Dy)) (some (piece0.node (1 - piece0.Dy))) := by
  refine ⟨junction1_validC, highPos_of_valid _ _ _ _ junction1_q ?_, junction1_q, junction1_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction1_highL⟩
  · exact ⟨_, junction1_highR⟩

def junction2_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p .leaf (.p (.p .leaf .leaf) .leaf))), .leaf, (.p .leaf (.p .leaf (.p (.p .leaf .leaf) .leaf)))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction2_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction2_validC : SourceValidC (piece2.node 0) (piece1.node (1 - piece1.Dy)) (some (piece1.node (1 - piece1.Dy))) := by decide +kernel
theorem junction2_highL : HighCertAt (piece2.node 0) (piece1.node (1 - piece1.Dy)) (piece1.node (1 - piece1.Dy)) 8 (crossing (piece2.node 0) (piece1.node (1 - piece1.Dy))) junction2_treesL := by
  decide +kernel
theorem junction2_highR : HighCertAt (piece2.node 0) (piece1.node (1 - piece1.Dy)) (piece1.node (1 - piece1.Dy)) 8 (piece2.node 0).cap junction2_treesR := by
  decide +kernel
theorem junction2_q : (piece2.node 0).q < 3/4 := by decide +kernel
theorem junction2_cell : CellRatio (piece2.node 0) (piece1.node (1 - piece1.Dy)) := by decide +kernel
theorem junction2_valid : SourceValid2 (piece2.node 0) (piece1.node (1 - piece1.Dy)) (some (piece1.node (1 - piece1.Dy))) := by
  refine ⟨junction2_validC, highPos_of_valid _ _ _ _ junction2_q ?_, junction2_q, junction2_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction2_highL⟩
  · exact ⟨_, junction2_highR⟩

def junction3_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p (.p .leaf (.p .leaf .leaf)) .leaf)), .leaf, (.p .leaf (.p (.p .leaf (.p .leaf .leaf)) .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction3_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction3_validC : SourceValidC (piece3.node 0) (piece2.node (1 - piece2.Dy)) (some (piece2.node (1 - piece2.Dy))) := by decide +kernel
theorem junction3_highL : HighCertAt (piece3.node 0) (piece2.node (1 - piece2.Dy)) (piece2.node (1 - piece2.Dy)) 8 (crossing (piece3.node 0) (piece2.node (1 - piece2.Dy))) junction3_treesL := by
  decide +kernel
theorem junction3_highR : HighCertAt (piece3.node 0) (piece2.node (1 - piece2.Dy)) (piece2.node (1 - piece2.Dy)) 8 (piece3.node 0).cap junction3_treesR := by
  decide +kernel
theorem junction3_q : (piece3.node 0).q < 3/4 := by decide +kernel
theorem junction3_cell : CellRatio (piece3.node 0) (piece2.node (1 - piece2.Dy)) := by decide +kernel
theorem junction3_valid : SourceValid2 (piece3.node 0) (piece2.node (1 - piece2.Dy)) (some (piece2.node (1 - piece2.Dy))) := by
  refine ⟨junction3_validC, highPos_of_valid _ _ _ _ junction3_q ?_, junction3_q, junction3_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction3_highL⟩
  · exact ⟨_, junction3_highR⟩

def junction4_treesL : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![(.p .leaf (.p (.p (.p .leaf .leaf) .leaf) .leaf)), .leaf, (.p .leaf (.p (.p (.p .leaf .leaf) .leaf) .leaf))]] : Fin 2 → Fin 3 → Split) k.1 k.2
def junction4_treesR : Branch → Split := fun k => (![![.leaf, .leaf, .leaf], ![.leaf, .leaf, .leaf]] : Fin 2 → Fin 3 → Split) k.1 k.2
theorem junction4_validC : SourceValidC (piece4.node 0) (piece3.node (1 - piece3.Dy)) (some (piece3.node (1 - piece3.Dy))) := by decide +kernel
theorem junction4_highL : HighCertAt (piece4.node 0) (piece3.node (1 - piece3.Dy)) (piece3.node (1 - piece3.Dy)) 8 (crossing (piece4.node 0) (piece3.node (1 - piece3.Dy))) junction4_treesL := by
  decide +kernel
theorem junction4_highR : HighCertAt (piece4.node 0) (piece3.node (1 - piece3.Dy)) (piece3.node (1 - piece3.Dy)) 8 (piece4.node 0).cap junction4_treesR := by
  decide +kernel
theorem junction4_q : (piece4.node 0).q < 3/4 := by decide +kernel
theorem junction4_cell : CellRatio (piece4.node 0) (piece3.node (1 - piece3.Dy)) := by decide +kernel
theorem junction4_valid : SourceValid2 (piece4.node 0) (piece3.node (1 - piece3.Dy)) (some (piece3.node (1 - piece3.Dy))) := by
  refine ⟨junction4_validC, highPos_of_valid _ _ _ _ junction4_q ?_, junction4_q, junction4_cell⟩
  intro h hh b hb
  simp only [Option.mem_def, Option.some.injEq] at hh
  subst hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ⟨_, junction4_highL⟩
  · exact ⟨_, junction4_highR⟩


end QRH.RepeatedMarks.Faceless
