import Research.UnforcedRestart.«actual-forcing-budget».Main
import Research.UnforcedRestart.«difference-equation».Main
import Research.UnforcedRestart.«energy-comparison».Main
import Research.UnforcedRestart.«gronwall-threshold».Main
import Research.UnforcedRestart.«local-theory-obstruction».Main
import Research.UnforcedRestart.«periodic-restart-data».Main
import Research.UnforcedRestart.«pressure-absorption».Main
import Research.UnforcedRestart.«r3-restart-data».Main
import Research.UnforcedRestart.«scaling-and-compactness».Main
import Research.UnforcedRestart.«smooth-force-cutoff».Main
import Research.UnforcedRestart.«strong-norm-growth-transfer».Main
import Research.UnforcedRestart.«time-translation».Main
import Lean.Util.CollectAxioms

/-! Validation tooling, not an additional mathematical theorem. Enumerate every
constant belonging to every imported project/research module, including generated
helpers, and check its complete axiom closure. External library modules are listed
separately; their unused metaprogramming constants are not mathematical exports. -/
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
            throwError "Forbidden axiom {ax} in {name}"
        let axText := String.intercalate "," (axioms.toList.map Name.toString)
        logInfo m!"COVERAGE\t{mod}\t{name}\t[{axText}]"
        count := count + 1
  unless count > 0 do
    throwError "Empty dependency coverage"
  logInfo m!"COVERAGE_COUNT\t{count}"
