import Lean

/-!
# Comparator Test Runner

Runs integration tests for the comparator from `tests/projects/`.
Each test project is a directory containing:
- `Challenge.lean` / `Solution.lean`: the Lean source files
- `config.json`: the comparator configuration
- `test.json`: expected exit code, e.g. `{"exit_code": 0}` for a passing test
- (optional) `lakefile.toml`: custom lake configuration; a default is generated if absent

## Usage

```bash
# Run all tests
lean --run runtests.lean

# Run only tests whose name contains "simple" or "def_hole"
lean --run runtests.lean simple def_hole
```
-/

open Lean System.FilePath IO.FS IO.Process System

structure TestConfig where
  exit_code : Nat
  expected_output : Option (Array String) := none
  expected_json_output : Option Lean.Json := none
  two_phase_cli_snapshot : Option String := none
  simulate_agent_edit : Option (String × String) := none
  tamper_snapshot_header : Option String := none
  deriving FromJson, ToJson

inductive TestResult
  | success (projectName : String)
  | failure (projectName : String) (expected : Nat) (actual : Nat) (output : String)
  | error (projectName : String) (message : String)

def copyFile (src : FilePath) (dst : FilePath) : IO Unit := do
  let contents ← IO.FS.readBinFile src
  IO.FS.writeBinFile dst contents

partial def copyDirContents (src : FilePath) (dst : FilePath) : IO Unit := do
  let entries ← System.FilePath.readDir src
  for entry in entries do
    let srcPath := entry.path
    let relativeName := entry.fileName
    let dstPath := dst / relativeName

    if (← srcPath.isDir) then
      IO.FS.createDirAll dstPath
      copyDirContents srcPath dstPath
    else
      copyFile srcPath dstPath

def createAdditionalFiles (dir : FilePath) : IO Unit := do
  -- Only generate a default lakefile if the test project doesn't provide its own
  if !(← (dir / "lakefile.toml").pathExists) then
    let lakefileContent :=
"
name = \"comparatortest\"
version = \"0.1.0\"

[[lean_lib]]
name = \"Solution\"

[[lean_lib]]
name = \"Challenge\"
"
    IO.FS.writeFile (dir / "lakefile.toml") lakefileContent

def runCommandInDir (dir : FilePath) (cmd : String) (args : Array String) : IO (Nat × String) := do
  let out ← IO.Process.output {
    cmd := cmd
    args := args
    cwd := some dir
  }
  pure (out.exitCode.toNat, out.stdout ++ "\n" ++ out.stderr)

/-- `expected` matches `actual` structurally, except that an expected string ending in `*` matches any
actual string with that prefix (used for kernel messages, whose pretty-printed terms are not part of
the contract and change between Lean versions). -/
partial def jsonMatches (expected actual : Json) : Bool :=
  match expected, actual with
  | .str e, .str a => if e.endsWith "*" then a.startsWith (e.dropEnd 1).toString else e == a
  | .obj e, .obj a =>
    e.size == a.size && e.all fun k v => match a.get? k with | some v' => jsonMatches v v' | none => false
  | .arr e, .arr a => e.size == a.size && (e.zip a).all fun (x, y) => jsonMatches x y
  | e, a => e == a

def readTestConfig (configPath : FilePath) : IO TestConfig := do
  let content ← IO.FS.readFile configPath
  match Lean.Json.parse content with
  | .error e => throw <| IO.userError s!"Failed to parse JSON: {e}"
  | .ok json =>
    match Lean.fromJson? json with
    | .error e => throw <| IO.userError s!"Failed to decode config: {e}"
    | .ok cfg => pure cfg

def getTempDir : IO FilePath := do
  return "/tmp" / s!"lean_test_{← IO.rand 0 999999}"

def runTestProject (projectPath : FilePath) (projectName : String) (repoDir : FilePath)
    (comparatorPath : FilePath) : IO TestResult := do
  let mut tempDirCreated := none
  try
    let configPath := projectPath / "test.json"
    let config ← readTestConfig configPath

    let tempDir ← getTempDir
    IO.FS.createDirAll tempDir
    tempDirCreated := some tempDir

    copyDirContents projectPath tempDir

    copyFile (repoDir / "lean-toolchain") (tempDir / "lean-toolchain")

    createAdditionalFiles tempDir

    IO.FS.createDirAll (tempDir / ".lake")
    if (← IO.FS.readFile (tempDir / "lakefile.toml")).contains "mathlib" then
      let (updateExit, updateOut) ← runCommandInDir tempDir "lake" #["update"]
      if updateExit != 0 then
        IO.FS.removeDirAll tempDir
        return TestResult.error projectName s!"lake update exited with {updateExit}:\n{updateOut}"
      let (cacheExit, cacheOut) ← runCommandInDir tempDir "lake" #["exe", "cache", "get"]
      if cacheExit != 0 then
        IO.println s!"Warning: lake exe cache get exited with {cacheExit}:\n{cacheOut}"

    let (exitCode, outputTrace) ← if let some snap := config.two_phase_cli_snapshot then
      let (exit1, out1) ← runCommandInDir tempDir "lake" #["env", comparatorPath.toString, "--snapshot", snap, "config.json"]
      if exit1 != 0 then
        pure (exit1, out1)
      else
        if let some (src, dst) := config.simulate_agent_edit then
          copyFile (tempDir / src) (tempDir / dst)
        if let some header := config.tamper_snapshot_header then
          let snapPath := tempDir / snap
          let rest := ((← IO.FS.readFile snapPath).splitOn "\n").drop 1
          IO.FS.writeFile snapPath (String.intercalate "\n" (header :: rest))
        let (exit2, out2) ← runCommandInDir tempDir "lake" #["env", comparatorPath.toString, "--verify", snap, "config.json"]
        pure (exit2, out1 ++ "\n" ++ out2)
    else
      runCommandInDir tempDir "lake" #["env", comparatorPath.toString, "config.json"]

    -- If expected_output substrings are specified, verify they exist in the trace
    if let some expectedSubstrings := config.expected_output then
      for substr in expectedSubstrings do
        if !outputTrace.contains substr then
          IO.FS.removeDirAll tempDir
          return TestResult.error projectName s!"Expected output trace substring '{substr}' was not found.\nCaptured output:\n{outputTrace}"

    -- If a json_output_path was configured, verify the output file exists and is valid JSON.
    let projectConfigPath := projectPath / "config.json"
    if (← projectConfigPath.pathExists) then
      let projectConfigContent ← IO.FS.readFile projectConfigPath
      let optPath : Option String := do
        let json ← (Lean.Json.parse projectConfigContent).toOption
        json.getObjValAs? String "json_output_path" |>.toOption
      if let some jsonOutputPath := optPath then
        let actualOutputPath := tempDir / jsonOutputPath
        if !(← actualOutputPath.pathExists) then
          IO.FS.removeDirAll tempDir
          return TestResult.error projectName s!"json_output_path file '{jsonOutputPath}' was not created"
        match Lean.Json.parse (← IO.FS.readFile actualOutputPath) with
        | .error e =>
          IO.FS.removeDirAll tempDir
          return TestResult.error projectName s!"json_output_path file '{jsonOutputPath}' contains invalid JSON: {e}"
        | .ok outputJson =>
          if let some expectedJson := config.expected_json_output then
            if !jsonMatches expectedJson outputJson then
              IO.FS.removeDirAll tempDir
              return TestResult.error projectName s!"JSON mismatch.\nExpected: {expectedJson}\nGot: {outputJson}"

    IO.FS.removeDirAll tempDir

    if exitCode == config.exit_code then
      return TestResult.success projectName
    else
      return TestResult.failure projectName config.exit_code exitCode outputTrace

  catch e =>
    if let some tempDir := tempDirCreated then
      try IO.FS.removeDirAll tempDir catch _ => pure ()
    return TestResult.error projectName e.toString

def findProjects (testsDir : FilePath) : IO (Array FilePath) := do
  let projectsDir := testsDir / "projects"
  if !(← projectsDir.pathExists) then
    throw <| IO.userError s!"Projects directory not found: {projectsDir}"

  let entries ← System.FilePath.readDir projectsDir
  let mut projects := #[]
  for entry in entries do
    if (← entry.path.isDir) then
      projects := projects.push entry.path
  pure projects

def printTestResult (result : TestResult) : IO Unit := do
  match result with
  | .success name =>
    IO.println s!"✓ {name}: PASSED"
  | .failure name expected actual output =>
    IO.println s!"✗ {name}: FAILED (expected exit code {expected}, got {actual})\nOutput:\n{output}"
  | .error name msg =>
    IO.println s!"✗ {name}: ERROR - {msg}"

/-- Run comparator integration tests. When `args` is non-empty, only tests whose
project name contains one of the given strings (as a substring) are executed. -/
def main (args : List String) : IO UInt32 := do
  let repoDir : FilePath := (← IO.getEnv "COMPARATOR_REPO_DIR").map FilePath.mk |>.getD "."
  let testsDir : FilePath := repoDir / "tests"
  let filters := args

  IO.println "# Running tests\n"

  let allProjects ← findProjects testsDir

  let projects := if filters.isEmpty then
    allProjects
  else
    allProjects.filter fun p => filters.any (p.fileName.get!.contains ·)

  if projects.isEmpty then
    if filters.isEmpty then
      IO.println "No projects found!"
    else
      IO.println s!"No projects matching {filters} found!"
    return 1

  let comparatorPath ← IO.FS.realPath <| repoDir / ".lake" / "build" / "bin" / "comparator"

  let mut allPassed := true
  let mut results := #[]
  for projectPath in projects do
    let projectName := projectPath.fileName.get!
    IO.println s!"\n## Running test: {projectName}\n"
    let result ← runTestProject projectPath projectName repoDir comparatorPath
    results := results.push result
    match result with
    | .success _ => pure ()
    | _ => allPassed := false

  IO.println "\n# Summary\n"

  for result in results do
    printTestResult result

  IO.println ""
  if allPassed then
    IO.println "All tests passed!"
    return 0
  else
    IO.println "Some tests failed."
    return 1
