/-!
Tests statement and disproof comparison when Lean generates declaration-scoped or helper-cached
internal auxiliary constants (`_proof_N`, `match_N`):
1. `nested_proof`: nested tactic proof (`by omega`) inside a theorem binder (`_proof_1`).
2. `let_matcher`: destructuring `let` in a theorem statement (`match_1`).
3. `helper_cached_matcher`: `match` in a theorem statement whose shape is cached under an earlier
   `private` helper in `Solution.lean`.
4. `poly_matcher`: universe-polymorphic destructuring `let` followed by a second universe parameter
   `v` (where `Challenge`'s matcher has 2 level params and `Solution`'s specialized matcher has 1).
5. `ulift_matcher_collapse`: two distinct matchers in `Challenge` (`ULift.{u}` vs `ULift.{0}`)
   that collapse into a single reused matcher in `Solution` when disproven at `u = 0`.
6. `direct_proof_helper_matcher`: direct proof (not `.disproof`) where an earlier `private` helper
   in `Solution.lean` caches `.match_1` first.
-/

universe u v

-- 1. Nested proof in statement (`nested_proof._proof_1`)
theorem nested_proof (l : Nat) (t : Fin (l + 1) → Int) (h0 : t ⟨0, by omega⟩ = -1) :
    t ⟨0, by omega⟩ = 1 := by
  sorry

-- 2. Destructuring `let` in statement (`let_matcher.match_1`)
def runWitness (n : Nat) : Nat × Nat := (n, n + 1)

theorem let_matcher (n : Nat) :
    let (a, b) := runWitness n
    a = b := by
  sorry

-- 3. `match` expression cached under an earlier helper in `Solution`
def pairFn (k : Nat) : Int × Int := (Int.ofNat k, -Int.ofNat k)

theorem helper_cached_matcher (k : Nat) :
    (match pairFn k with | (a, b) => a + b) = 1 := by
  sorry

-- 4. Universe-polymorphic destructuring `let` + trailing universe parameter `v`
theorem poly_matcher (α : Type u) (p : α × α) (β : Type v) (x y : β) :
    (let (a, b) := p; a = b) ∧ x = y := by
  sorry

-- 5. Two matchers in `Challenge` collapsing into one matcher in `Solution` at `u = 0`
theorem ulift_matcher_collapse (p : ULift.{u} Nat × Nat) (q : ULift.{0} Nat × Nat) :
    (let (a, b) := p; a.down + b) + (let (c, d) := q; c.down + d) = 1 := by
  sorry

-- 6. Direct proof where an earlier `private` helper in `Solution` caches `.match_1`
theorem direct_proof_helper_matcher (p : Bool × Bool) :
    (let (a, b) := p; a == b) = (p.1 == p.2) := by
  sorry
