import SamplingLowerBounds
import Lean.Util.CollectAxioms

/- Enumerate the imported project declarations, independently of Audit.lean.
This prevents an omitted entry in the hand-readable audit from hiding a hole. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    if (`SamplingLowerBounds).isPrefixOf name && info.isTheorem then
      count := count + 1
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
  if count == 0 then throwError "No project declarations were imported"
  logInfo m!"PASS: all {count} project theorem declarations use only standard Lean axioms."
