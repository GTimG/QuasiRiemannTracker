/- Copyright (c) 2026 ArviFoxy. Apache-2.0. -/
import Submissions.arvi_selected_leaf.JointDetector.Notices

/-!
# Sources and attribution

The selected-leaf development (`R1/`, `Leaf`, `Step`, `Price`, `Combine`, `Unselected`, `Gates`, `Curve`,
`NativeStart`, `Final`) is by ArviFoxy; the research and the Lean development were AI-assisted. Reused source keeps
its authorship, copyright notices and license (Apache-2.0):

* `JointDetector/`: 114 modules of Joseph Bebel's joint-detector-fine-chain (PR 93,
  `submissions/2026-10-28-joint-detector-fine-chain/src/Candidate/Local/Qrh/JointDetector/`), copied unchanged
  except for the module paths in their `import` lines, so that they can be imported from this package (the selected
  sextic norm, the fine detector words and counts, the refined supplier). Its notices and the Apache-2.0 text are
  in `JointDetector/Notices.lean`.
* `Return/`: 14 modules of arvi-density's return (`submissions/2026-10-29-arvi-density`, `arvi_density/Return/`),
  unchanged except for the imports and the retuned constants in `Return/Constants.lean`. That return follows Sil's
  generic return (sil-density-split) and Hailey Collet's final stage; the rest of it (`arvi_density/ReturnD/`) is
  imported from arvi-density unchanged.
* `Tuning/`: the certificate of the retuned return (three windows), generated for these constants; it follows
  arvi-density's reflective return certificate.
* `NativeStart`: Sil's native cube-free step (sil-density-split, as assembled in Jacob Sussman's
  density-split-fine-chain) from the fourth-power source of arvi-repeated-marks-on-sil-face (on Sil's
  fourth-power face), with the continuous induction of the selected-leaf line.
* The OpenAI framework (openai-baseline) and Hailey Collet's source, counting and return machinery
  (hailey-collet-1252270103) underlie all of it.
-/
