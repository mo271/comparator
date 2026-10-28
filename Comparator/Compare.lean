/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Comparator.Axioms
import Export.Parse

open Lean

namespace Comparator

/-- Whether `n` is a compiler/elaborator-generated internal auxiliary constant (`_proof_N`,
`match_N`, `eq_N`, `_auxLemma`, etc.), stripping any module-local `_private.<mod>.0` prefix first
so user-named `private` helpers are not treated as anonymous auxiliaries. Configured
`definitionTargets` are never treated as auxiliaries. -/
def isAuxName (defTargets : Std.HashSet Name) (n : Name) : Bool :=
  !defTargets.contains n && ((Lean.privateToUserName? n).getD n).isInternalDetail

/-- Extracts `(thmVal, levels, args)` when `e` is an application spine (including 0 arguments)
headed by an internal auxiliary theorem in `env`. -/
def auxThmApp? (defTargets : Std.HashSet Name) (env : Export.ExportedEnv) (e : Expr) :
    Option (TheoremVal × List Level × Array Expr) :=
  match e.getAppFn with
  | .const n ls =>
    if isAuxName defTargets n then
      match env.constMap[n]? with
      | some (.thmInfo c) =>
        if ls.length == c.levelParams.length then some (c, ls, e.getAppArgs) else none
      | _ => none
    else none
  | _ => none

/-- Peels `args.size` leading `forallE` binders from `type` and substitutes `args` simultaneously
via `Expr.instantiateRev`. -/
def instantiateForallPrefix (type : Expr) (args : Array Expr) : Option Expr := Id.run do
  let mut curr := type
  for _ in [:args.size] do
    match curr with
    | .forallE _ _ body _ => curr := body
    | _ => return none
  return some (curr.instantiateRev args)

structure MatchState where
  verifiedPairs : Std.HashSet ((Name × List Level) × (Name × List Level)) := {}
  visiting : Std.HashSet (Name × Name) := {}
  nonAuxSet : Std.HashSet Name := {}
  nonAuxConsts : Array Name := #[]

abbrev MatchM := StateT MatchState Option

@[inline]
def addNonAux (n : Name) : MatchM Unit := do
  if !(← get).nonAuxSet.contains n then
    modify fun s => { s with nonAuxSet := s.nonAuxSet.insert n, nonAuxConsts := s.nonAuxConsts.push n }

/-- Records all non-auxiliary constants (including `Expr.proj` structure names) transitively
referenced by an expression `e` in `chal`, so unused arguments eliminated during auxiliary theorem
instantiation still have their constants verified by `Compare.loop`. -/
partial def collectChalNonAux (defTargets : Std.HashSet Name) (chal : Export.ExportedEnv)
    (e : Expr) (visitedAux : Std.HashSet Name := {}) : MatchM (Std.HashSet Name) := do
  match e with
  | .const n _ =>
    if isAuxName defTargets n then
      if visitedAux.contains n then return visitedAux
      let visitedAux := visitedAux.insert n
      match chal.constMap[n]? with
      | some (.thmInfo c) => collectChalNonAux defTargets chal c.type visitedAux
      | some (.defnInfo d) =>
        if d.safety == .safe then
          let visitedAux ← collectChalNonAux defTargets chal d.type visitedAux
          collectChalNonAux defTargets chal d.value visitedAux
        else
          addNonAux n
          return visitedAux
      | _ => addNonAux n; return visitedAux
    else
      addNonAux n
      return visitedAux
  | .app f a =>
    let visitedAux ← collectChalNonAux defTargets chal f visitedAux
    collectChalNonAux defTargets chal a visitedAux
  | .lam _ t b _ | .forallE _ t b _ =>
    let visitedAux ← collectChalNonAux defTargets chal t visitedAux
    collectChalNonAux defTargets chal b visitedAux
  | .letE _ t v b _ =>
    let visitedAux ← collectChalNonAux defTargets chal t visitedAux
    let visitedAux ← collectChalNonAux defTargets chal v visitedAux
    collectChalNonAux defTargets chal b visitedAux
  | .proj s _ b =>
    addNonAux s
    collectChalNonAux defTargets chal b visitedAux
  | .mdata _ b => collectChalNonAux defTargets chal b visitedAux
  | _ => return visitedAux

/-- Structurally compares `e1` (in `chal`) and `e2` (in `sol`) modulo internal auxiliary constants:
- Internal auxiliary theorem applications (`.thmInfo`, even when `abstractNestedProofs` captured
  different subsets of local hypotheses) are paired by matching their universe- and argument-
  instantiated types (sound by proof irrelevance; the solution theorem and arguments are still
  axiom- and kernel-checked).
- Safe internal auxiliary definitions (`.defnInfo`, such as `.match_N`) are paired by matching both
  their universe-instantiated types and bodies (sound by kernel delta-reduction; `DefinitionVal.all`
  is intentionally not restricted to `[d.name]` because metaprograms like Mathlib's `@[to_dual]` and
  `@[to_additive]` copy matcher definitions without rewriting `all`, while `visiting` forbids cycles
  on either side). Non-safe internal `.defnInfo`s (`partial`/`unsafe`) must match by exact name and
  are delegated to `Compare.loop`.
All matched non-auxiliary constants (including projection structure names) are recorded in
`nonAuxConsts` for `Compare.loop`. -/
partial def matchExpr (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (e1 e2 : Expr) (ctx1 : Array Expr := #[]) : MatchM Unit := do
  let thmApp1 := auxThmApp? defTargets chal e1
  let thmApp2 := auxThmApp? defTargets sol e2
  if thmApp1.isSome || thmApp2.isSome then
    let some (c1, ls1, args1) := thmApp1 | failure
    let some (c2, ls2, args2) := thmApp2 | failure
    let key := ((c1.name, ls1), (c2.name, ls2))
    guard (!(← get).visiting.any fun (a, b) => a == c1.name || b == c2.name)
    let c1TypeInst := c1.type.instantiateLevelParams c1.levelParams ls1
    let c2TypeInst := c2.type.instantiateLevelParams c2.levelParams ls2
    let directMatch : MatchM Unit := do
      guard (args1.size == args2.size)
      if !(← get).verifiedPairs.contains key then
        modify fun s => { s with visiting := s.visiting.insert (c1.name, c2.name) }
        matchExpr defTargets chal sol c1TypeInst c2TypeInst #[]
        modify fun s => { s with
          visiting := s.visiting.erase (c1.name, c2.name)
          verifiedPairs := s.verifiedPairs.insert key
        }
      for i in [:args1.size] do
        matchExpr defTargets chal sol args1[i]! args2[i]! ctx1
    let instantiatedMatch : MatchM Unit := do
      let some inst1 := instantiateForallPrefix c1TypeInst args1 | failure
      let some inst2 := instantiateForallPrefix c2TypeInst args2 | failure
      if !defTargets.isEmpty then
        let mut curr := c1TypeInst
        for i in [:args1.size] do
          let .bvar idx := args1[i]! | failure
          guard (idx < ctx1.size)
          let .forallE _ dom body _ := curr | failure
          let bvarType := ctx1[ctx1.size - 1 - idx]!.liftLooseBVars 0 (idx + 1)
          let domInst := dom.instantiateRev (args1.extract 0 i)
          guard (((matchExpr defTargets chal chal bvarType domInst ctx1).run ({} : MatchState)).isSome)
          curr := body
      let vis ← collectChalNonAux defTargets chal c1TypeInst {}
      let _ ← args1.foldlM (fun v a => collectChalNonAux defTargets chal a v) vis
      modify fun s => { s with visiting := s.visiting.insert (c1.name, c2.name) }
      matchExpr defTargets chal sol inst1 inst2 ctx1
      modify fun s => { s with visiting := s.visiting.erase (c1.name, c2.name) }
    directMatch <|> instantiatedMatch
    return ()
  match e1, e2 with
  | .app f1 a1, .app f2 a2 =>
    matchExpr defTargets chal sol f1 f2 ctx1
    matchExpr defTargets chal sol a1 a2 ctx1
  | .lam _ t1 b1 _, .lam _ t2 b2 _
  | .forallE _ t1 b1 _, .forallE _ t2 b2 _ =>
    matchExpr defTargets chal sol t1 t2 ctx1
    matchExpr defTargets chal sol b1 b2 (ctx1.push t1)
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    matchExpr defTargets chal sol t1 t2 ctx1
    matchExpr defTargets chal sol v1 v2 ctx1
    matchExpr defTargets chal sol b1 b2 (ctx1.push t1)
  | .proj s1 i1 b1, .proj s2 i2 b2 =>
    guard (s1 == s2 && i1 == i2)
    addNonAux s1
    matchExpr defTargets chal sol b1 b2 ctx1
  | .mdata d1 b1, .mdata d2 b2 =>
    guard (d1 == d2)
    matchExpr defTargets chal sol b1 b2 ctx1
  | .const n1 ls1, .const n2 ls2 =>
    let isAux1 := isAuxName defTargets n1
    let isAux2 := isAuxName defTargets n2
    if isAux1 || isAux2 then
      guard (isAux1 && isAux2)
      match chal.constMap[n1]?, sol.constMap[n2]? with
      | some (.defnInfo d1), some (.defnInfo d2) =>
        if d1.safety == .safe && d2.safety == .safe then
          let key := ((n1, ls1), (n2, ls2))
          if (← get).verifiedPairs.contains key then return ()
          guard (!(← get).visiting.any fun (a, b) => a == n1 || b == n2)
          guard (ls1.length == d1.levelParams.length && ls2.length == d2.levelParams.length)
          modify fun s => { s with visiting := s.visiting.insert (n1, n2) }
          matchExpr defTargets chal sol
            (d1.type.instantiateLevelParams d1.levelParams ls1)
            (d2.type.instantiateLevelParams d2.levelParams ls2) #[]
          matchExpr defTargets chal sol
            (d1.value.instantiateLevelParams d1.levelParams ls1)
            (d2.value.instantiateLevelParams d2.levelParams ls2) #[]
          modify fun s => { s with
            visiting := s.visiting.erase (n1, n2)
            verifiedPairs := s.verifiedPairs.insert key
          }
        else
          guard (n1 == n2 && ls1 == ls2 && d1.safety == d2.safety)
          addNonAux n1
      | some (.thmInfo _), _ | _, some (.thmInfo _)
      | some (.defnInfo _), _ | _, some (.defnInfo _) => failure
      | _, _ =>
        guard (n1 == n2 && ls1 == ls2)
        addNonAux n1
    else
      guard (n1 == n2 && ls1 == ls2)
      addNonAux n1
  | .bvar .., .bvar .. | .fvar .., .fvar .. | .mvar .., .mvar .. | .sort .., .sort .. | .lit .., .lit .. =>
    guard (e1 == e2)
  | _, _ => failure

def runMatchExpr (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (e1 e2 : Expr) : Option (Array Name) := do
  let ((), st) ← (matchExpr defTargets chal sol e1 e2).run {}
  return st.nonAuxConsts

partial def matchLevel (l1 l2 : Level) (params : List Name) (subst : List (Name × Level)) : List (Name × Level) :=
  match l1, l2 with
  | .param n, _ => if params.contains n && !subst.any (·.1 == n) then (n, l2) :: subst else subst
  | .succ n1, .succ n2 => matchLevel n1 n2 params subst
  | .max n1 n2, .max m1 m2 => matchLevel n2 m2 params (matchLevel n1 m1 params subst)
  | .max n1 n2, l2 => matchLevel n2 l2 params (matchLevel n1 l2 params subst)
  | .imax n1 n2, .imax m1 m2 => matchLevel n2 m2 params (matchLevel n1 m1 params subst)
  | .imax n1 n2, l2 => matchLevel n2 l2 params (matchLevel n1 l2 params subst)
  | _, _ => subst

/-- Infers universe-level instantiations for `chalLevels` by walking `e1` and `e2` in lockstep,
recursing into paired auxiliary declarations' instantiated types/values rather than zipping their
constant level lists directly (since specialized auxiliaries in `sol` may have fewer universe
parameters than polymorphic auxiliaries in `chal`). -/
partial def inferDisproofLevels (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (chalLevels : List Name) (e1 e2 : Expr)
    (subst : List (Name × Level) := [])
    (visiting : Std.HashSet (Name × Name) := {}) : List (Name × Level) :=
  match auxThmApp? defTargets chal e1, auxThmApp? defTargets sol e2 with
  | some (c1, ls1, args1), some (c2, ls2, args2) =>
    if visiting.any fun (a, b) => a == c1.name || b == c2.name then subst
    else
      let visiting' := visiting.insert (c1.name, c2.name)
      let c1TypeInst := c1.type.instantiateLevelParams c1.levelParams ls1
      let c2TypeInst := c2.type.instantiateLevelParams c2.levelParams ls2
      match instantiateForallPrefix c1TypeInst args1, instantiateForallPrefix c2TypeInst args2 with
      | some inst1, some inst2 =>
        inferDisproofLevels defTargets chal sol chalLevels inst1 inst2 subst visiting'
      | _, _ =>
        if args1.size == args2.size then
          let subst := inferDisproofLevels defTargets chal sol chalLevels c1TypeInst c2TypeInst subst visiting'
          (args1.zip args2).foldl (fun acc (a1, a2) =>
            inferDisproofLevels defTargets chal sol chalLevels a1 a2 acc visiting') subst
        else subst
  | some _, none | none, some _ => subst
  | none, none =>
    match e1, e2 with
    | .sort l1, .sort l2 => matchLevel l1 l2 chalLevels subst
    | .const n1 ls1, .const n2 ls2 =>
      let isAux1 := isAuxName defTargets n1
      let isAux2 := isAuxName defTargets n2
      if isAux1 || isAux2 then
        if isAux1 && isAux2 && !(visiting.any fun (a, b) => a == n1 || b == n2) then
          let visiting' := visiting.insert (n1, n2)
          match chal.constMap[n1]?, sol.constMap[n2]? with
          | some (.defnInfo d1), some (.defnInfo d2) =>
            if d1.safety == .safe && d2.safety == .safe
                && ls1.length == d1.levelParams.length && ls2.length == d2.levelParams.length then
              let subst := inferDisproofLevels defTargets chal sol chalLevels
                (d1.type.instantiateLevelParams d1.levelParams ls1)
                (d2.type.instantiateLevelParams d2.levelParams ls2) subst visiting'
              inferDisproofLevels defTargets chal sol chalLevels
                (d1.value.instantiateLevelParams d1.levelParams ls1)
                (d2.value.instantiateLevelParams d2.levelParams ls2) subst visiting'
            else if n1 == n2 && ls1.length == ls2.length then
              (ls1.zip ls2).foldl (fun acc (l1, l2) => matchLevel l1 l2 chalLevels acc) subst
            else subst
          | _, _ =>
            if n1 == n2 && ls1.length == ls2.length then
              (ls1.zip ls2).foldl (fun acc (l1, l2) => matchLevel l1 l2 chalLevels acc) subst
            else subst
        else subst
      else if n1 == n2 && ls1.length == ls2.length then
        (ls1.zip ls2).foldl (fun acc (l1, l2) => matchLevel l1 l2 chalLevels acc) subst
      else subst
    | .app f1 a1, .app f2 a2 =>
      let subst := inferDisproofLevels defTargets chal sol chalLevels f1 f2 subst visiting
      inferDisproofLevels defTargets chal sol chalLevels a1 a2 subst visiting
    | .lam _ d1 b1 _, .lam _ d2 b2 _
    | .forallE _ d1 b1 _, .forallE _ d2 b2 _ =>
      let subst := inferDisproofLevels defTargets chal sol chalLevels d1 d2 subst visiting
      inferDisproofLevels defTargets chal sol chalLevels b1 b2 subst visiting
    | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
      let subst := inferDisproofLevels defTargets chal sol chalLevels t1 t2 subst visiting
      let subst := inferDisproofLevels defTargets chal sol chalLevels v1 v2 subst visiting
      inferDisproofLevels defTargets chal sol chalLevels b1 b2 subst visiting
    | .mdata _ b1, .mdata _ b2
    | .proj _ _ b1, .proj _ _ b2 =>
      inferDisproofLevels defTargets chal sol chalLevels b1 b2 subst visiting
    | _, _ => subst

def checkDisproof (defTargets : Std.HashSet Name) (chal sol : Export.ExportedEnv)
    (chalType : Expr) (chalLevels : List Name) (solType : Expr) (solLevels : List Name) :
    Option (Array Name) :=
  let checkExp (outerConst : Name) (exp : Expr) : Option (Array Name) := do
    let expInst := exp.instantiateLevelParams solLevels (solLevels.map .param)
    let subst := inferDisproofLevels defTargets chal sol chalLevels chalType expInst
    let levels := chalLevels.map fun n => (subst.lookup n).getD Level.zero
    let chalTypeInst := chalType.instantiateLevelParams chalLevels levels
    let ((), st) ← (do
      addNonAux outerConst
      matchExpr defTargets chal sol chalTypeInst expInst).run {}
    return st.nonAuxConsts
  match solType with
  | .forallE _ exp (.const ``False []) _ => checkExp ``False exp
  | .app (.const ``Not []) exp => checkExp ``Not exp
  | _ => none

namespace Compare

structure Context where
  challenge : Export.ExportedEnv
  solution : Export.ExportedEnv
  definitionTargets : Std.HashSet Lean.Name

structure State where
  worklist : Array Lean.Name
  checked : Std.HashSet Lean.Name

abbrev CompareM := ReaderT Context <| StateT State <| Except String

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def addWorklist (n : Lean.Name) : CompareM Unit := do
  if !(← get).checked.contains n then
    modify fun s => { worklist := s.worklist.push n, checked := s.checked.insert n }

def addRelevantConsts (info : Lean.ConstantInfo) : CompareM Unit := do
  runForUsedConsts info addWorklist

partial def loop : CompareM Unit := do
  if (← get).worklist.isEmpty then
    return ()

  let target ← modifyGet fun s => (s.worklist.back!, { s with worklist := s.worklist.pop })
  let some challengeConst := (← read).challenge.constMap[target]?
    | throw s!"Const not found in challenge '{target}'"
  let some solutionConst := (← read).solution.constMap[target]?
    | throw s!"Const not found in solution '{target}'"

  let ctx ← read
  if ctx.definitionTargets.contains solutionConst.name then
    let .defnInfo cd := challengeConst
      | throw s!"Const does not match between challenge and target '{target}'"
    let .defnInfo sd := solutionConst
      | throw s!"Const does not match between challenge and target '{target}'"
    unless cd.name == sd.name && cd.levelParams == sd.levelParams && cd.safety == sd.safety do
      throw s!"Const does not match between challenge and target '{target}'"
    let some nonAuxConsts := runMatchExpr ctx.definitionTargets ctx.challenge ctx.solution cd.type sd.type
      | throw s!"Const does not match between challenge and target '{target}'"
    nonAuxConsts.forM addWorklist
  else
    match challengeConst, solutionConst with
    | .thmInfo cc, .thmInfo sc =>
      unless cc.name == sc.name && cc.levelParams == sc.levelParams do
        throw s!"Const does not match between challenge and target '{target}'"
      let some nonAuxConsts := runMatchExpr ctx.definitionTargets ctx.challenge ctx.solution cc.type sc.type
        | throw s!"Const does not match between challenge and target '{target}'"
      nonAuxConsts.forM addWorklist
    | .defnInfo cd, .defnInfo sd =>
      unless cd.name == sd.name && cd.levelParams == sd.levelParams && cd.safety == sd.safety do
        throw s!"Const does not match between challenge and target '{target}'"
      let some ((), st) := (do
          matchExpr ctx.definitionTargets ctx.challenge ctx.solution cd.type sd.type
          matchExpr ctx.definitionTargets ctx.challenge ctx.solution cd.value sd.value).run {}
        | throw s!"Const does not match between challenge and target '{target}'"
      st.nonAuxConsts.forM addWorklist
    | _, _ =>
      unless challengeConst == solutionConst do
        throw s!"Const does not match between challenge and target '{target}'"
      addRelevantConsts solutionConst

  loop

end Compare

def compareAt (challenge solution : Export.ExportedEnv) (theoremTargets : Array Lean.Name)
    (definitionTargets : Array Lean.Name) (primitive : Array Lean.Name) (allowDisproofs : Bool := false)
    (checked : Std.HashSet Lean.Name := {}) : Except String (Std.HashSet Lean.Name) := do
  let defTargetSet := Std.HashSet.ofArray definitionTargets
  let mut worklist := primitive

  for target in theoremTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let dname := target ++ `disproof
    if allowDisproofs && solution.constMap[dname]?.isSome then
      let some solutionConst := solution.constMap[dname]?
        | unreachable!
      let .thmInfo cc := challengeConst
        | throw s!"Challenge target is not a theorem: '{target}'"
      let .thmInfo sc := solutionConst
        | throw s!"Solution disproof target is not a theorem: '{dname}'"

      let some nonAuxConsts :=
          checkDisproof defTargetSet challenge solution cc.type cc.levelParams sc.type sc.levelParams
        | throw s!"Solution disproof statement does not match accepted disproof interface: '{dname}'"

      worklist := worklist ++ nonAuxConsts
    else
      let some solutionConst := solution.constMap[target]?
        | throw s!"Const not found in solution: '{target}'"
      let (cc, sc) ←
        match challengeConst, solutionConst with
        | .thmInfo cc, .thmInfo sc => pure (cc.toConstantVal, sc.toConstantVal)
        | .axiomInfo cc, .axiomInfo sc =>
          if cc.isUnsafe != sc.isUnsafe then
            throw s!"Challenge and solution theorem statement do not match: '{target}'"
          pure (cc.toConstantVal, sc.toConstantVal)
        | _, _ => throw s!"Challenge and solution constant kind don't match: '{target}'"

      if cc.name != sc.name || cc.levelParams != sc.levelParams then
        throw s!"Challenge and solution theorem statement do not match: '{target}'"
      let some nonAuxConsts := runMatchExpr defTargetSet challenge solution cc.type sc.type
        | throw s!"Challenge and solution theorem statement do not match: '{target}'"

      worklist := worklist ++ nonAuxConsts

  for target in definitionTargets do
    let some challengeConst := challenge.constMap[target]?
      | throw s!"Const not found in challenge: '{target}'"

    let some solutionConst := solution.constMap[target]?
      | throw s!"Const not found in solution: '{target}'"

    let .defnInfo challengeConst := challengeConst
      | throw s!"Challenge constant is not a definition: '{target}'"
    let .defnInfo solutionConst := solutionConst
      | throw s!"Solution constant is not a definition: '{target}'"

    if challengeConst.name != solutionConst.name
        || challengeConst.levelParams != solutionConst.levelParams
        || challengeConst.safety != solutionConst.safety then
      throw s!"Const does not match between challenge and target '{target}'"
    let some _ := runMatchExpr defTargetSet challenge solution challengeConst.type solutionConst.type
      | throw s!"Const does not match between challenge and target '{target}'"

    worklist := worklist.push solutionConst.name

  let (_, s) ← (do worklist.forM Compare.addWorklist; Compare.loop).run
    { challenge, solution, definitionTargets := defTargetSet } |>.run { worklist := #[], checked }
  return s.checked

end Comparator
