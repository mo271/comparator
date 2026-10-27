# Comparator
Comparator is a trustworthy judge for Lean proofs. It relies on having an existing Lean installation as
well as:
1. [`landrun`](https://github.com/Zouuup/landrun), compiled from the `main` branch's source, present in `PATH`
2. [`lean4export`](https://github.com/leanprover/lean4export/), at a version that is compatible with whatever Lean version your project is targeting, present in `PATH`
3. (optional) [nanoda](https://github.com/ammkrn/nanoda_lib/), compiled with a recent version of Rust.
   This is only necessary if you want to check with the nanoda kernel in addition to the builtin one.
   `cargo build --release` will place `nanoda_bin` in the `target/release` directory of the checked-out directory,
   this directory must be present in `PATH`

> [!NOTE]
> Alternatively full paths to these binaries can be specified using `COMPARATOR_LANDRUN`,
> `COMPARATOR_LEAN4EXPORT`, and `COMPARATOR_NANODA`. Comparator expects the compiled `query_decls`
> helper next to its own binary by default; use `COMPARATOR_QUERY_DECLS` to override that binary path
> when deploying it elsewhere.

Comparator is configured through a JSON file:
```
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["todo1"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```
Where `Challenge.lean` contains at least a theorem named `todo1` that has a `sorry` (or any other proof)
and `Solution.lean` is provided by a party trying to convince you that they have proven `todo1` by
writing out the same theorem but with a proper proof attached.

The following optional configuration fields control target selection and reporting:
- `definition_names`: definitions that the solution must fill in.
- `allow_disproofs`: when `true`, a theorem target `foo` may instead be solved by a theorem named
  `foo.disproof` of type `TargetTypeInstance → False` or `¬ TargetTypeInstance` (see [Disproofs](#disproofs)).
- `must_resolve_all_sorries`: defaults to `true`. When `false`, failed theorem targets are reported as
  warnings and a submission is accepted if at least one theorem target succeeds. Definition targets
  remain mandatory.
- `json_output_path`: writes a JSON verification report to the given path (see [JSON report](#json-report)).

If and only if both `theorem_names` and `definition_names` are omitted, comparator discovers targets
automatically. It selects theorems and reducible definitions declared in the challenge whose values
contain `sorryAx`. Opaque declarations are not selected as definition holes. Comparator rejects a
challenge when no verification target is selected or found.

Given the following assumptions:
1. The transitive closure of imports of `Challenge.lean` as well as `lakefile.toml`/`lakefile.lean`
   are controlled by you or trustworthy.
2. You have not previously tried to compile the `Solution` file or any other potentially adversarial
   files (as that might compromise your `Challenge` file to make it seem like you are looking for a
   different proof than you actually are)
3. You have the `landrun` and `lean4export` binary in `PATH`
4. `landrun` works correctly on your system and `Solution.lean` does not
   exploit any bugs in `landrun` that allow a process to escape its sandbox
5. The Lean kernel is correct (with `external_kernels` this can be reduced to
   "At least one of the Lean kernel or the `external_kernels` is correct")
6. You are not running this under a privileged user

If the following command succeeds:
```
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty -E PATH="$PATH" --working-directory $(pwd) -- bash -c 'lake env path/to/comparator/binary path/to/config.json'
```

Every theorem target accepted from `Solution` is guaranteed to:
1. Prove the same statement as provided in `Challenge`, or disprove an accepted universe instance of it
   when `allow_disproofs` is enabled
2. Use no more axioms than listed in `permitted_axioms`
3. Be accepted by the Lean kernel

With the default `must_resolve_all_sorries: true`, a successful comparator run means that every selected
theorem target was accepted. With `must_resolve_all_sorries: false`, inspect the warnings or JSON report
to determine which theorem targets were accepted.

### JSON report

With `json_output_path`, comparator writes a report of the form
```
{
  "accepted": false,
  "error": "Some verification targets failed:\n- t2: (some (Comparator.CheckFailure.kernel \"lean\" \"...\"))\n",
  "outcomes": [["t1", {"failureMode": null, "mode": "direct", "solutionName": "t1", ...}],
               ["t2", {"failureMode": {"kernel": {"kernel": "lean", "message": "..."}}, ...}]]
}
```
- `accepted` is `true` if and only if the run succeeded (exit code `0`). It is the only success signal:
  with `must_resolve_all_sorries: false` an accepted run may contain failed targets, and a rejected run
  may contain fully verified ones.
- `outcomes` has one entry per verification attempt, keyed by target name (a theorem target with both a
  direct proof and a `.disproof` has two). `failureMode: null` means the attempt passed every phase,
  including the kernel replay. The kernel phase is reported per target: `kernel` with `"lean"` carries the
  kernel's message for the target itself or for the first rejected declaration in its dependency closure,
  so a bogus shared helper marks every target that uses it and no other. Failures that cannot be attributed
  to a target (`reexport`, a rejection by one of the `external_kernels`) mark every target that was still
  accepted.
- The file is written atomically, and a placeholder with `accepted: false` is written as soon as
  comparator starts, so a stale or partial report can never be mistaken for a success.

> [!NOTE]
> The Trusted Code Base of Landrun naturally includes the operating system and hardware it is running on, plus its sandboxing mechanism.
> The systemd-run part explicitly guard against a vulnerability in landrun, Comparator's current sandboxing solution, that will be fixed in Linux 7.1

Note that running `lake exe cache get` to download a Mathlib cache is acceptable before running the
comparator if you trust the cache to not be modified as to, e.g. contain different definitions from
the one you would expect.

Furthermore, it is possible to avoid trusting `landrun`'s ability to sandbox the `Solution.lean` file:
if you have obtained a fully pre-built `.lake` directory through other means and without compromising your
checking environment, `Solution.lean` will not be rebuilt.

## Two-Phase Clean-Room Verification
To fully protect trusted challenge specifications from adversarial filesystem modifications or tampering by untrusted agents, comparator supports a two-phase clean-room execution workflow using a single pack file (`.pack`).

1. **Phase 1 (Pre-Run Snapshot):** Before running the untrusted agent, compile and snapshot the challenge environment inside a trusted clean container:
   ```sh
   comparator --snapshot snapshot.pack path/to/config.json
   ```
   This captures the autodiscovered target names and trusted kernel export stream into a single compact plain-text archive.

2. **Phase 2 (Post-Run Verification):** After the agent has finished executing and generated `Solution.lean`, run verification against the trusted snapshot:
   ```sh
   comparator --verify snapshot.pack path/to/config.json
   ```
   Comparator will directly ingest the trusted `snapshot.pack` and skip compiling or querying `Challenge.olean`. This completely neutralizes any attempts by the agent to tamper with imported dependencies or redefine challenge targets.

## Checking with Additional Kernels
Comparator can additionally check solutions with external kernels. To do this you must register them
in the `external_kernels` list:
```
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["todo1"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
    "external_kernels": {
        "mykernel": ["kernel_bin", "--threads=4", "--paranoid"]
    }
}
```
Comparator will execute the command described by the `mykernel` array and additionally pass a
file, containing the solution export to the kernel, in this case: `kernel_bin --threads=4 --paranoid export.ndjson`

For backwards compatibility reasons users may instead set `enable_nanoda: true` to obtain a config
that calls `nanoda_bin`. Furthermore, comparator currently attempts to detect `nanoda`-style kernels
by checking whether the name contains the string `noda` and instead passing a `nanoda`-style
`config.json` to them. This is only intended as a migration path while the kernel ecosystem
moves toward having an option to receive the input file as a `CLI` argument.

For development purposes, comparator supports overriding `nanoda` specifically using the
`COMPARATOR_NANODA` environment variable.
## Definition Holes
Sometimes challenges want to leave open definitions for solutions to fill in. This can range from
simple things like filling in a `Prop` valued definition to resolve whether a conjecture is true or
false, all the way to constructing complex mathematical objects. For these types of solutions,
comparator can guarantee that:
1. They use no more axioms than listed in `permitted_axioms`
2. They are accepted by the Lean kernel
3. The name, type, universe levels and safety levels of all definition holes match

Crucially, many definition hole challenges can be gamed without additional oversight.
For example, given a conjecture-style challenge:
```lean
def ChallengeSolution : Prop := sorry
theorem challenge : RiemannHypothesis ↔ ChallengeSolution := sorry
```
a solution could define `ChallengeSolution` as:
```lean
def ChallengeSolution : Prop := RiemannHypothesis
```
and conduct a simple proof of `challenge` by reflexivity. The intention of the challenge though was
of course to ask for a `True` or `False` value for `ChallengeSolution`. For this reason, all
definition hole solutions **must** always be checked with an additional (potentially human)
verifier.

To establish a definition hole, the challenge must provide it as a sorried definition:
```lean
def large : Nat := sorry

theorem large_lt : 37 < large := sorry
```
All of the holes must then be put into the `definition_names` field in `configuration.json`:
```
{
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["large_lt"],
    "definition_names": ["large"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```
For all `definition_names`, comparator ensures that in the solution:
- the name, type, universe levels and safety level match
- the constant does not (transitively) refer to non-permitted axioms
- the constant type checks

Thus, the following solution would be accepted:
```lean
def large : Nat := 38

theorem large_lt : 37 < large := by decide
```

## Disproofs

When `allow_disproofs` is `true`, a theorem target may be replaced by a theorem with the `.disproof`
suffix:
```lean
theorem foo.disproof (h : TargetType) : False := by
  ...
```
Equivalently, the disproof may have type `¬ TargetType`. Comparator checks that `TargetType`
syntactically matches an instance of the target theorem's type (up to binder names/annotations and
compiler-generated internal auxiliary constants such as `_proof_N` and `match_N`, which are paired
when their theorem types or definition types and bodies match).
To obtain `TargetType`, run `#check @target` and copy the complete type after the colon into the `h` binder,
being careful not to introduce custom typeclass instances before `foo.disproof` that would change
synthesized instances (e.g., replacing `Classical.propDecidable`).

`TargetType` may instantiate the target theorem's universe parameters. This models the
existential universe choice needed to refute a theorem that claims to hold polymorphically at every
universe level.

## Development

The `scripts/fake-landrun.sh` can be used to replace Landrun in development if you are not on a Linux system that supports landrun.

The following commands, starting from the root directory of a fresh git checkout, will build and run `comparator` on one of the test examples:

```sh
lake build lean4export comparator query_decls

cd tests/projects/simple_mismatch

cat > lakefile.toml <<EOF
name = "comparatortest"
version = "0.1.0"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "Challenge"
EOF

COMPARATOR_LANDRUN=$(realpath ../../../scripts/fake-landrun.sh) COMPARATOR_LEAN4EXPORT=$(realpath ../../../.lake/packages/lean4export/.lake/build/bin/lean4export) lake env ../../../.lake/build/bin/comparator config.json
```

The following commands, starting from the root directory of a fresh git checkout, will build and run the tests:

```sh
lake build lean4export comparator query_decls
COMPARATOR_LANDRUN=$(realpath scripts/fake-landrun.sh) COMPARATOR_LEAN4EXPORT=$(realpath .lake/packages/lean4export/.lake/build/bin/lean4export) lean --run runtests.lean
```

Replace the `landrun` and `lean4export` arguments as needed, or place the binaries in `PATH`.

## Internals
We generally adopt a policy of not loading olean files as they just get mmaped into our address
space and then dereferenced and are as such a potential point of attack for sophisticated adversaries.

The comparator performs the following steps to ensure these properties:
1. Build `Challenge` using `lake` in a `landrun` sandbox that has:
   - read access to the entire file system and write access to `/dev`
   - write access to the `.lake` directory of the project
2. Inspect declarations in the produced `Challenge.olean` using the compiled `query_decls` helper in a
   sandboxed subprocess. The helper is separate from comparator so `.olean` deserialization cannot be
   called accidentally inside the trusted parent process.
3. Run `lean4export` on the produced `Challenge.olean` in a `landrun` sandbox that has:
   - read access to the entire file system and write access to `/dev`
4. Repeat the same build, declaration inspection and export steps with `Solution`
5. Verify that all declarations used in the statement of all relevant theorems in `Challenge`
   are the same as in the `Solution` environment.
   This always includes the declarations from `Init` with special meaning to the kernel. Both `Challenge`
   and `Solution` therefore need to import the default prelude.
6. Verify that the body of all relevant theorems in the `Solution` environment only uses axioms
   listed in `permitted_axioms`
7. Replay the `Solution` environment into the Lean kernel. Doing this within the same process as the
   comparator should be safe as the worst thing that can happen at this point is an exploit that
   makes the kernel accept when it should reject and that same exploit should also be applicable
   from within an external process.

Note that as `Challenge` is trusted, both the sandbox and lean4export step for `Challenge` are not
necessary to the best of our knowledge. We still adopt these rather free measures as additional
paranoia in case an adversary comes up with a means of attack anyway.

## Acknowledgement
Comparator was originally developed by Lean FRO, with feedback from the AIMO team, in support of the
AIMO series of competitions and their goal of enabling trustworthy LLM Lean evaluation on Kaggle.
