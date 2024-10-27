import Mathlib.Computability.RegularExpressions

namespace TransitionSystems

  @[reducible]
  def RegexProp (α : Type) := RegularExpression (α → Bool)


  namespace RegexProp

    inductive PMatches {α} : RegexProp α → List α → Prop
    | matchEpsilon : PMatches .epsilon []
    | matchChar {p : α → Bool} {x : α} : p x → PMatches (.char p) [x]
    | matchPlusLeft {r₁ r₂ : RegexProp α} {s : List α} :
        PMatches r₁ s → PMatches (r₁ + r₂) s
    | matchPlusRight {r₁ r₂} {s : List α} :
        PMatches r₂ s → PMatches (r₁ + r₂) s
    | matchComp {r₁ r₂ : RegexProp α} {s₁ s₂ : List α} :
        PMatches r₁ s₁ → PMatches r₂ s₂ → PMatches (r₁ * r₂) (s₁ ++ s₂)
    | matchStarNil (r : RegexProp α) : PMatches (.star r) []
    | matchStarCons {r : RegexProp α} {x : α} {xs xs' : List α} :
        PMatches r (x :: xs) → PMatches (.star r) xs' → PMatches (.star r) ((x :: xs) ++ xs')

    @[reducible]
    def charAny {α} : RegexProp α := .char (fun _ => true)

    @[simp]
    theorem pmatches_epsilon {α} : @PMatches α .epsilon [] := by constructor

    @[simp]
    theorem pmatches_char_cons {α} {p : α → Bool} {x : α} {xs : List α} :
        PMatches (.char p) (x :: xs) ↔ p x ∧ xs = [] := by
      apply Iff.intro <;> intro h
      · cases h ; tauto
      · cases xs <;> tauto

    @[simp]
    theorem pmatches_char_cons' {α} {p : α → Bool} {xs : List α} :
        PMatches (.char p) xs ↔ ∃ x, p x ∧ xs = [x] := by
      cases xs <;> simp
      · intro h ; cases h
      · rename_i x _ ; apply Iff.intro
        · intro ; exists x ; tauto
        · intro ⟨x', _⟩ ; cc


    @[simp]
    theorem pmatches_plus {α} {r₁ r₂ : RegexProp α} {xs : List α} :
        PMatches (r₁ + r₂) xs ↔ PMatches r₁ xs ∨ PMatches r₂ xs := by
      apply Iff.intro <;> intro h <;> cases h <;> tauto
      apply PMatches.matchPlusRight ; assumption


    theorem pmatches_comp {α} {r₁ r₂ : RegexProp α} {xs : List α} :
        PMatches (r₁ * r₂) xs ↔ ∃ xs₁ xs₂,
          xs = xs₁ ++ xs₂ ∧ PMatches r₁ xs₁ ∧ PMatches r₂ xs₂ := by
      apply Iff.intro
      · intro h ; cases h ; rename_i xs₁ xs₂ _ _ ; exists xs₁, xs₂
      · intro ⟨xs₁, xs₂, happ, _, _⟩ ; rw [happ] ; constructor <;> assumption


    @[simp]
    theorem pmatches_comp_char_cons {α} {p : α → Bool} {r : RegexProp α} {x : α} {xs : List α} :
        PMatches ((.char p) * r) (x :: xs) ↔ p x ∧ PMatches r xs := by
      apply Iff.intro <;> simp [pmatches_comp]
      · intros ; simp [*] at * ; cc
      · intros ; exists [x], xs ; tauto

    @[simp]
    theorem pmatches_zero_comp {α} {r : RegexProp α} {xs : List α} : ¬ PMatches (0 * r) xs := by
      intro ; contradiction

    @[simp]
    theorem pmatches_zero_plus {α} {r : RegexProp α} {xs : List α} : PMatches (0 + r) xs ↔ PMatches r xs := by
      simp [pmatches_plus] ; intro ; contradiction

    @[simp]
    theorem pmatches_one_comp {α} {r : RegexProp α} {xs : List α} :
        PMatches (1 * r) xs ↔ PMatches r xs := by
      apply Iff.intro <;> intro h
      · cases h ; rename_i h₁ h₂ ; cases h₁ ; exact h₂
      · rw [←List.nil_append xs] ; tauto

    /-
      This approach to deciding RegexProps is almost 1:1 with
      https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/RegularExpressions.html#RegularExpression.deriv
    -/

    /-- `r.pderiv a` matches `x` if `r` matches `a :: x`, the Brzozowski derivative of `r` with respect
  to `a`. -/
    def pderiv {α} : RegexProp α → α → RegexProp α
    | .zero, _ => .zero
    | .epsilon, _ => .zero
    | .char p, x => if p x then .epsilon else .zero
    | .plus r₁ r₂, x => (pderiv r₁ x) + (pderiv r₂ x)
    | .comp r₁ r₂, x =>
        if r₁.matchEpsilon then (pderiv r₁ x * r₂ + pderiv r₂ x) else (pderiv r₁ x * r₂)
    | .star r, x => pderiv r x * .star r


    @[simp]
    theorem pderiv_zero {α} (x : α) : pderiv 0 x = 0 := rfl

    @[simp]
    theorem pderiv_one {α} (x : α) : pderiv 1 x = 0 := rfl

    @[simp]
    theorem pderiv_char {α} (p : α → Bool) (x : α) :
      pderiv (.char p) x = if p x then 1 else 0 := by simp [pderiv]

    -- @[simp]
    -- theorem pderiv_char_true {α} (p : α → Bool) (x : α) (h : p x = true) : pderiv (.char p) x = 1 :=
    --   by simp [pderiv, h]

    -- @[simp]
    -- theorem pderiv_char_true' {α} (p : α → Prop) {_ : DecidablePred p} (x : α) (h : p x) :
    --   pderiv (.char (fun x => decide (p x))) x = 1 := by simp [pderiv, h]

    -- @[simp]
    -- theorem pderiv_char_false {α} (p : α → Bool) (x : α) (h : p x = false) : pderiv (.char p) x = 0 :=
    --   by simp [pderiv, h]

    --     @[simp]
    -- theorem pderiv_char_false' {α} (p : α → Prop) {_ : DecidablePred p} (x : α) (h : ¬ p x) :
    --   pderiv (.char (fun x => decide (p x))) x = 0 := by simp [pderiv, h]

    @[simp]
    theorem pderiv_plus {α} (r₁ r₂ : RegexProp α) (x : α) :
        pderiv (r₁ + r₂) x = pderiv r₁ x + pderiv r₂ x := rfl

    @[simp]
    theorem pderiv_star {α} (r : RegexProp α) (x : α) :
        pderiv (.star r) x = (pderiv r x) * (.star r) := rfl


    def rpmatch {α} : RegexProp α → List α → Bool
    | r, [] => r.matchEpsilon
    | r, x :: xs => rpmatch (r.pderiv x) xs

    -- @[simp]
    theorem rpmatch_nil {α} (r : RegexProp α) :
        rpmatch r [] = r.matchEpsilon := rfl

    @[simp]
    theorem rpmatch_cons {α} (r : RegexProp α) (x : α) (xs : List α) :
        rpmatch r (x :: xs) = rpmatch (r.pderiv x) xs := rfl

    @[simp]
    theorem rpmatch_zero {α} (xs : List α) : rpmatch 0 xs = false := by
      induction xs <;> tauto

    theorem one_rpmatch_iff {α} {xs : List α} :
        rpmatch 1 xs ↔ xs = [] := by
      cases xs <;> simp [rpmatch, RegularExpression.matchEpsilon]

    theorem char_rpmatch_iff {α} {p : α → Bool} {xs : List α} :
        rpmatch (.char p) xs ↔ ∃ x, xs = [x] ∧ p x := by
      cases xs <;> simp [rpmatch, pderiv, RegularExpression.matchEpsilon]
      rename_i x xs ; split <;> simp [*, one_rpmatch_iff] at *; tauto

    theorem plus_rpmatch_iff {α} {r₁ r₂ : RegexProp α} {xs : List α} :
        rpmatch (r₁ + r₂) xs ↔ rpmatch r₁ xs ∨ rpmatch r₂ xs := by
      induction xs generalizing r₁ r₂ <;> simp [rpmatch, RegularExpression.matchEpsilon]
      rename_i ih ; rw [ih]

    theorem comp_rpmatch_iff {α} {r₁ r₂ : RegexProp α} {xs : List α} :
        rpmatch (r₁ * r₂) xs ↔ ∃ xs₁ xs₂, xs = xs₁ ++ xs₂ ∧ rpmatch r₁ xs₁ ∧ rpmatch r₂ xs₂ := by
      induction xs generalizing r₁ r₂ <;> simp [rpmatch, RegularExpression.matchEpsilon]
      · apply Iff.intro ; tauto
        intro ⟨xs₁, xs₂, ⟨h₁, h₂⟩, h⟩; rw [h₁, h₂] at h ; exact h
      · rename_i x xs ih ; simp [pderiv] ; split
        · apply Iff.intro
          · rw [plus_rpmatch_iff, ih] ; intro h ; apply Or.elim h
            · intro ⟨xs₁, xs₂, _⟩ ; exists x :: xs₁, xs₂ ; tauto
            · intro ; exists [] ; tauto
          · rw [plus_rpmatch_iff, ih] ; simp ; intros xs₁ xs₂ ; intros
            cases xs₁ <;> simp [*] at *
            · right ; rw [←rpmatch] ; cc
            · left ; rename_i xs₁ _ _ ; exists xs₁, xs₂ ; cc
        · rw [ih] ; apply Iff.intro <;> intro ⟨xs₁, xs₂, _⟩
          · exists x :: xs₁, xs₂ ; tauto
          · cases xs₁
            · simp [rpmatch, *] at *
            · rename_i xs₁ h ; simp at h ; exists xs₁, xs₂ ; cc

    @[simp]
    theorem rpmatch_star_nil {α} (r : RegexProp α) : rpmatch (.star r) [] = true := by rfl

    theorem rpmatch_star_once {α} {r : RegexProp α} {xs : List α} :
        rpmatch r xs → rpmatch (.star r) xs := by
        cases xs <;> simp [rpmatch, comp_rpmatch_iff, RegularExpression.matchEpsilon]
        case cons x xs => intro ; exists xs, [] ; simp ; tauto

    theorem star_rpmatch_cons_rpmatch {α} {r : RegexProp α} {x : α} {xs : List α} :
        rpmatch (.star r) (x :: xs) →
        ∃ xs₁ xs₂, xs = xs₁ ++ xs₂ ∧ rpmatch r (x :: xs₁) ∧ rpmatch (.star r) xs₂ := by
      simp [rpmatch, comp_rpmatch_iff]

    theorem cons_rpmatch_star_rpmatch {α} {r : RegexProp α} {xs₁ xs₂ : List α} :
        rpmatch r xs₁ → rpmatch (.star r) xs₂
        → rpmatch (.star r) (xs₁ ++ xs₂) := by
      cases xs₁ <;> simp [rpmatch, comp_rpmatch_iff]
      rename_i x xs₁ ; intro h₁ h₂ ; exists xs₁, xs₂

    theorem star_rpmatch_iff {α} {r : RegexProp α} {xs : List α} :
        rpmatch (.star r) xs
        ↔ ∃ xss : List (List α), xss.join = xs ∧ ∀ xs' ∈ xss, rpmatch r xs' := by
      apply Iff.intro
      · have ⟨n, hn⟩ : ∃ n, xs.length ≤ n := ⟨xs.length, le_rfl⟩
        induction n generalizing xs <;> cases xs <;> simp at *
        case zero.nil | succ.nil => exists [] ; tauto
        case succ.cons n ih x xs =>
          intro h
          have ⟨xs₁, xs₂, hxs, h₁, h₂⟩ := star_rpmatch_cons_rpmatch h
          have hn₂ : xs₂.length ≤ n := le_trans (by simp [*]) hn
          have ⟨xss, hjoin, hxss⟩ := ih hn₂ h₂
          exists (x :: xs₁) :: xss ; simp [*] ; exact hxss
      · intro ⟨xss, hjoin, hxss⟩ ; induction xss generalizing xs
        all_goals simp [*] at *
        · rw [hjoin] ; exact rpmatch_star_nil r
        · rw [←hjoin] ; rename_i ih ; exact cons_rpmatch_star_rpmatch hxss.1 (ih hxss.2)

    theorem rpmatch_pmatches_iff {α} {r : RegexProp α} {xs : List α} :
        rpmatch r xs = true ↔ PMatches r xs := by
      induction r generalizing xs
      case zero => simp ; intro h ; cases h
      case epsilon =>
        simp [one_rpmatch_iff] ; apply Iff.intro <;> intro h
        · rw [h] ; constructor
        · cases h ; rfl
      case char x =>
        simp [char_rpmatch_iff]
        apply Iff.intro <;> intro ⟨x, _⟩ <;> exists x <;> tauto
      case plus _ _ ihxs₁ ihxs₂ => simp [plus_rpmatch_iff, ihxs₁, ihxs₂]
      case comp _ _ ihxs₁ ihxs₂ =>
        simp [comp_rpmatch_iff, ihxs₁, ihxs₂] ; apply Iff.intro
        · intro ⟨_, _, h, _, _⟩ ; rw [h] ; constructor <;> assumption
        · intro h ; cases h ; tauto
      case star r ih =>
        simp [star_rpmatch_iff, ih] ; clear ih ; apply Iff.intro
        · intro ⟨xss, hjoin, hxss⟩ ; induction xss generalizing xs
          · simp at hjoin ; rw [hjoin] ; constructor
          · simp at hjoin ; rw [←hjoin]
            rename_i xs₁ xss ih ; cases xs₁ ; simp at *
            · tauto
            · constructor ; apply hxss ; tauto
              exact ih (by rfl) (fun _ => by tauto)
        · have ⟨n, hn⟩: exists n, xs.length ≤ n := ⟨xs.length, le_rfl⟩
          intro h ; induction n generalizing xs <;> cases xs <;> simp at hn <;> cases h
          case matchStarNil | matchStarNil =>
            exists [] ; tauto
          case matchStarCons n ih x xs₁ xs₂ _ _ =>
            simp at hn ; specialize @ih xs₂ (by omega) (by assumption)
            let ⟨xss, _, _⟩ := ih
            exists (x :: xs₁) :: xss ; simpa [*]

    instance instDecidablePMatches {α} (r : RegexProp α) : DecidablePred r.PMatches := fun _ =>
      decidable_of_iff _ rpmatch_pmatches_iff


    theorem pmatches_cons {α} {r : RegexProp α} {x : α} {xs : List α} :
        PMatches r (x :: xs) ↔ PMatches (r.pderiv x) xs := by
      apply Iff.trans (Iff.symm rpmatch_pmatches_iff)
      apply Iff.trans _ (rpmatch_pmatches_iff)
      rfl

    @[simp]
    theorem pmatches_star_nil {α} {r : RegexProp α} : PMatches (.star r) [] := by constructor

    @[simp]
    theorem pmatches_star_cons {α} {r : RegexProp α} {x : α} {xs : List α} :
        PMatches (.star r) (x :: xs) ↔ PMatches (r.pderiv x * .star r) xs := pmatches_cons

    theorem star_induction
        {α} {r : RegexProp α} {p : List α → Prop} (xs : List α) (star_nil : p ∅)
        (star_cons : ∀ xs₁ xs₂, PMatches r xs₁ → PMatches (.star r) xs₂ → p xs₂ → p (xs₁ ++ xs₂))
        : PMatches (.star r) xs → p xs := by
      have ⟨n, hn⟩ : exists n, xs.length ≤ n := ⟨_, le_rfl⟩
      intro hxs; induction n generalizing xs
      · simp at hn ; rw [hn] ; exact star_nil
      · rename_i n ih ; cases xs <;> try simp [*]
        cases' hxs ; rename_i x xs₁ xs₂ h₂ h₁
        simp at hn
        apply star_cons (x :: xs₁) xs₂ h₁ h₂
        apply ih _ (by omega) h₂

  end RegexProp

end TransitionSystems
