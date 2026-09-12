import Research.UnforcedRestart.Round5.Acceptance
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    logInfo m!"MODULE\t{mod}"
    if mod.toString.startsWith "ComparatorChallenges" then
      throwError "Forbidden challenge import: {mod}"
  let entries := env.constants.toList.mergeSort (fun a b => Name.quickLt a.1 b.1)
  let mut count : Nat := 0
  for (name, info) in entries do
    if let some idx := env.getModuleIdxFor? name then
      let mod := env.header.moduleNames[idx.toNat]!
      let project := ["NavierStokes", "Euler", "Common", "Research"].any fun root =>
        mod.toString == root || mod.toString.startsWith (root ++ ".")
      if project then
        if info.isUnsafe then
          throwError "Unsafe project dependency: {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Forbidden dependency {ax} in {name}"
        let axText := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"COVERAGE\t{mod}\t{name}\t[{axText}]"
        count := count + 1
  unless count > 0 do
    throwError "Empty dependency coverage"
  logInfo m!"COVERAGE_COUNT\t{count}"
