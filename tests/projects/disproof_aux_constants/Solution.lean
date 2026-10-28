-- 1. Disproof of `nested_proof`: mints `nested_proof.disproof._proof_1`
theorem nested_proof.disproof
    (h : ∀ (l : Nat) (t : Fin (l + 1) → Int), t ⟨0, by omega⟩ = -1 → t ⟨0, by omega⟩ = 1) : False := by
  exact absurd (h 0 (fun _ => -1) rfl) (by decide)

-- 2. Disproof of `let_matcher`: mints `let_matcher.disproof.match_1`
def runWitness (n : Nat) : Nat × Nat := (n, n + 1)

theorem let_matcher.disproof
    (h : ∀ (n : Nat), let (a, b) := runWitness n; a = b) : False := by
  have := h 0
  dsimp [runWitness] at this
  omega

-- 3. `myHelper` mints `_private.Solution.0.myHelper.match_1` first, and
--    `helper_cached_matcher.disproof` reuses it
def pairFn (k : Nat) : Int × Int := (Int.ofNat k, -Int.ofNat k)

private theorem myHelper (p : Int × Int) : (match p with | (a, b) => a + b) = p.1 + p.2 := rfl

theorem helper_cached_matcher.disproof
    (h : ∀ (k : Nat), (match pairFn k with | (a, b) => a + b) = 1) : False := by
  have := h 0
  rw [myHelper] at this
  dsimp [pairFn] at this
  omega

-- 4. Disproof of `poly_matcher` specialized at `u = 0, v = 1`
theorem poly_matcher.disproof
    (h : ∀ (α : Type 0) (p : α × α) (β : Type 1) (x y : β),
      (let (a, b) := p; a = b) ∧ x = y) : False := by
  have ⟨h1, _⟩ := h Bool (true, false) PUnit.{2} PUnit.unit.{2} PUnit.unit.{2}
  cases h1

-- 5. Disproof of `ulift_matcher_collapse` specialized at `u = 0`
theorem ulift_matcher_collapse.disproof
    (h : ∀ (p : ULift.{0} Nat × Nat) (q : ULift.{0} Nat × Nat),
      (let (a, b) := p; a.down + b) + (let (c, d) := q; c.down + d) = 1) : False := by
  have := h (⟨0⟩, 0) (⟨0⟩, 0)
  omega

-- 6. Direct proof of `direct_proof_helper_matcher` with a helper-cached matcher
private theorem directHelper (p : Bool × Bool) : (let (a, b) := p; a && b) = (p.1 && p.2) := rfl

theorem direct_proof_helper_matcher (p : Bool × Bool) :
    (let (a, b) := p; a == b) = (p.1 == p.2) := by
  cases p
  rfl

-- 7. Disproof referencing a helper whose safe internal `.defnInfo` has `d.all != [d.name]`
mutual
  def dualAux.match_1 : Nat → Nat
    | 0 => 0
    | n + 1 => dualAux.match_2 n
  def dualAux.match_2 : Nat → Nat
    | 0 => 1
    | n + 1 => dualAux.match_1 n
end

def useDualAux (n : Nat) : Nat := dualAux.match_1 n

theorem mutual_all_aux_disproof.disproof
    (h : ∀ (n : Nat), useDualAux n = 1) : False := by
  have := h 0
  contradiction
