/-
  Some proofs relating different types of simulation for (hardware-based) transition systems.

  Lean-formalization of [A Framework for Microprocessor Correctness Statements](http://dx.doi.org/10.1007/3-540-44798-9_33).
  Following along with the paper, we model various forms of alignment for a generic match relation.
  Unlike the paper, we
  (1) consider relationships between the *inputs* to the specification and implementation transition systems
  (2) restrict the specification and implementation to both be deterministic

-/

import Mathlib.Data.List.Basic
import TransitionSystems.RegexProp

namespace TransitionSystems

  @[reducible]
  def Trace (α : Type) := List α

  class TransitionSystem (S W TS : Type) where
    start: TS → S
    step : TS → S → W → S


  namespace TransitionSystem

    variable {S W TS} [TransitionSystem S W TS]

    def run (m : TS) (s : S) : Trace W → Trace S
    | [] => []
    | w :: ws => let s' := step m s w ; s' :: (run m s' ws)

    @[simp]
    theorem run_nil (m : TS) (s : S) : run m s ([] : List W) = [] := rfl

    @[simp]
    theorem run_cons (m : TS) (s : S) (w : W) (ws : Trace W) :
      run m s (w :: ws) = step m s w :: run m (step m s w) ws := rfl


    inductive ValidRun (m : TS) : S → Trace W → Trace S → Prop where
      | done s : ValidRun m s [] []
      | step {s s' : S} {w : W} {ws : Trace W} {ss : Trace S} :
          s' = step m s w
          → ValidRun m s' ws ss
          → ValidRun m s (w :: ws) (s' :: ss)

    @[simp]
    theorem ValidRun_nil {m : TS} {s : S} {ss : Trace S} :
        ValidRun m s ([] : List W) ss ↔ ss = [] :=
      Iff.intro (fun h => by cases h ; rfl) (fun h => by rw [h] ; constructor)

    @[simp]
    theorem ValidRun_nil' {m : TS} {s : S} {ws : Trace W} :
        ValidRun m s ws [] ↔ ws = [] :=
      Iff.intro (fun h => by cases h ; rfl) (fun h => by rw [h] ; constructor)

    @[simp]
    theorem ValidRun_cons {m : TS} {s s' : S} {w : W} {ws : Trace W} {ss : Trace S} :
      ValidRun m s (w :: ws) (s' :: ss) ↔ s' = step m s w ∧ ValidRun m s' ws ss :=
        Iff.intro (fun h => by cases h ; tauto) (by tauto)

    theorem run_valid {m : TS} {s : S} {ws : Trace W} : ValidRun m s ws (run m s ws) := by
      induction ws generalizing s <;> simp ; tauto

    theorem valid_run_iff_run {m : TS} {s : S} {ws : Trace W} {ss : Trace S} :
        ValidRun m s ws ss ↔ ss = run m s ws := by
      apply Iff.intro <;> intro h
      · induction h <;> simp at * ; rename_i hs' _ _
        rw [←hs'] ; tauto
      · rw [h] ; exact run_valid

    theorem valid_run_unique {m : TS} {s : S} {ws : Trace W} {ss₁ ss₂ : Trace S} :
        ValidRun m s ws ss₁ → ValidRun m s ws ss₂ → ss₁ = ss₂ := by
      intros h₁ h₂
      induction ws generalizing s ss₁ ss₂
      all_goals (cases h₁ ; cases h₂ ; simp [*] at *)
      tauto

    theorem valid_run_append {m : TS} {s₁ s₂ : S} {ws : Trace W} {ss₁ ss₂ : Trace S} :
        ValidRun m s₁ ws (ss₁ ++ [s₂] ++ ss₂)
        ↔ ∃ ws₁ ws₂,
            ws = ws₁ ++ ws₂
            ∧ ValidRun m s₁ ws₁ (ss₁ ++ [s₂])
            ∧ ValidRun m s₂ ws₂ ss₂ := by
      apply Iff.intro
      · intro h ; induction ss₁ generalizing s₁ ws <;> simp at h
        · cases ws <;> simp at * ; rename_i w ws
          exists [w], ws ; tauto
        · cases ws <;> simp at * ; rename_i s₁' ss₁ w ws ih
          have ⟨ws₁, ws₂, hws, h₁, h₂⟩ := ih h.2
          exists w :: ws₁, ws₂ ; simp [*]
          rw [←h.1] ; exact h₁
      · intro ⟨ws₁, ws₂, hw, h₁, h₂⟩
        induction ss₁ generalizing s₁ ws ws₁ <;> cases ws₁ <;> simp at *
        · simp [h₁.2, *] at * ; tauto
        · cases ws <;> simp at hw ; rw [hw.1, hw.2] at * ; simp at *
          exact And.intro (h₁.1) (by tauto)

    theorem valid_run_length {m : TS} {s : S} {ws : Trace W} {ss : Trace S} :
        ValidRun m s ws ss → ws.length = ss.length := by
      intro h ; induction ws generalizing s ss <;> cases h <;> simp [*] ; tauto

  end TransitionSystem

  @[reducible]
  def TraceToFirst {α} (p : α → Bool) : RegexProp α := (.star (.char (! p ·)) * .char p)

  namespace TraceToFirst

    @[simp]
    theorem TraceToFirst_nil {α} {p : α → Bool} {x : α} :
        RegexProp.PMatches (TraceToFirst p) [x] ↔ p x := by
      apply Iff.intro ; intro h
      · have ⟨xs₁, xs₂, hx, h₁, h₂⟩ := RegexProp.pmatches_comp.mp h
        cases xs₁ <;> cases xs₂ <;> simp at *
        cases h₂ ; cc
      · intro hx ; apply RegexProp.pmatches_comp.mpr
        exists [], [x] ; simp [hx]

    theorem TraceToFirst_cons {α} {p : α → Bool} {x : α} {xs : Trace α} :
        (TraceToFirst p).PMatches xs → ¬ p x → (TraceToFirst p).PMatches (x :: xs) := by
      intro hxs hx ; simp [TraceToFirst] at *
      have ⟨xs₁, xs₂, hxs, h₁, h₂⟩ := RegexProp.pmatches_comp.mp hxs
      apply RegexProp.pmatches_comp.mpr
      exists (x :: xs₁), xs₂ ; simp [*]

    @[simp]
    theorem TraceToFirst_not_last {α} {p : α → Bool} {x : α} {xs : Trace α} {x' : α} :
        (TraceToFirst p).PMatches (x :: (xs ++ [x']))
        ↔ ! p x ∧ (TraceToFirst p).PMatches (xs ++ [x']) := by
      apply Iff.intro ; intro h
      · let ⟨xs₁, xs₂, hxs, h₁, h₂⟩ := RegexProp.pmatches_comp.mp h ; clear h
        cases h₂ ; rw [←List.cons_append] at hxs
        let ⟨hxs, hx'⟩ := List.append_inj' hxs rfl ; simp at hx'
        cases xs₁ <;> simp at hxs ; cases hxs ; subst x x' xs
        rename_i x' hx' x xs ; simp at h₁
        split at h₁ <;> simp at h₁ ; simp [*] ; tauto
      · intro ⟨hx, h⟩
        let ⟨xs₁, xs₂, hxs, h₁, h₂⟩ := RegexProp.pmatches_comp.mp h ; clear h
        cases h₂ ; let ⟨hxs, hx'⟩ := List.append_inj' hxs rfl ; simp at hx'
        subst xs x' ; rename_i x' hx' ; clear hxs
        change RegexProp.PMatches _ (([x] ++ _) ++ _) ; constructor <;> simp
        · split <;> simp [*] at *
        · exact hx'

    theorem TraceToFirst_last {α} {p : α → Bool} {xs : Trace α} :
        (TraceToFirst p).PMatches xs ↔ ∃ xs₁ x, xs = xs₁ ++ [x] ∧ p x ∧ ∀ x ∈ xs₁, ¬ p x := by
      apply Iff.intro
      · intro h ; cases h ; rename_i xs _ hxs hx
        cases hx ; rename_i x hx
        exists xs, x ; simp [hx] ; clear x hx
        induction xs <;> simp
        rename_i x xs ih ; simp at hxs
        split at hxs <;> simp at hxs ; tauto
      · intro ⟨xs₁, x, hxs, hx, hxs₁⟩ ; rw [hxs]
        constructor
        · clear x xs hx hxs ; induction xs₁ <;> simp [*]
          rename_i ih ; apply ih ; intro x hx ; apply hxs₁ ; tauto
        · tauto

    theorem trace_to_first {α} {p : α → Bool} {xs : Trace α} :
        (∃ x ∈ xs, p x) → ∃ (xs₁ xs₂ : Trace α),
          xs = xs₁ ++ xs₂ ∧ (TraceToFirst p).PMatches xs₁ := by
      intro hxs ; induction xs <;> simp at *
      rename_i x xs ih
      cases hp : p x
      · simp [hp] at hxs ; have ⟨x', hx', hp'⟩ := hxs
        have ⟨xs₁, ⟨xs₂, hxs⟩, hfst⟩ := ih x' hx' hp'
        exists (x :: xs₁); apply And.intro ⟨xs₂, by simp [hxs]⟩
        apply TraceToFirst_cons hfst ; cc
      · exists [x] ; apply And.intro ⟨xs, by simp⟩ (TraceToFirst_nil.mpr hp)

  end TraceToFirst


  namespace Alignment

    class ComposableTraceRmap {α β : Type} (Rw : Trace α → Trace β → Trace β → Prop) where
      Rw_init : Rw [] [] []
      Rw_compose : ∀ {tra₁ tra₂ trb₁ trb₂ trc₁ trc₂},
        Rw tra₁ trb₁ trc₁ ∧ Rw tra₂ trb₂ trc₂ ↔ Rw (tra₁ ++ tra₂) (trb₁ ++ trb₂) (trc₁ ++ trc₂)

    variable {W S₁ S₂ TS₁ TS₂}
    variable [TransitionSystem S₁ W TS₁] [TransitionSystem S₂ W TS₂]
    variable (impl : TS₁) (spec : TS₂)
    variable (R : S₁ → S₂ → Prop)
    variable (Rw : Trace S₁ → Trace W → Trace W → Prop)

    open TransitionSystem

    def FlushPointMatchInductiveStep (isFlushed: S₁ → Bool) : Prop :=
      ∀ {u u' : S₁} {v : S₂} {trw : Trace W} {tru : Trace S₁},
        R u v
        → ValidRun impl u trw (tru ++ [u'])
        → isFlushed u
        → isFlushed u'
        → ∃ trx trv v',
            Rw (u :: tru) trw trx
            ∧ ValidRun spec v trx (trv ++ [v'])
            ∧ R u' v'


    def MustIssueMatchInductiveStep
        (isStalled: S₁ → Bool) : Prop :=
      ∀ {u u' : S₁} {v : S₂} {trw : Trace W} {tru : Trace S₁} {w : W},
        R u v
        → ! isStalled u
        → ValidRun impl u (w :: trw) (tru ++ [u'])
        → (TraceToFirst (! isStalled ·)).PMatches (tru ++ [u'])
        → Rw (u :: tru) (w :: trw) [w]
          ∧ ∃ v', v' = step spec v w ∧ R u' v'


    def StutteringMatchInductiveStep : Prop :=
      ∀ {u u' : S₁} {v : S₂} {w : W},
        R u v
        → u' = step impl u w
        → ∃ v',
          (v' = v ∧ Rw [u] [w] []
          ∨ v' = step spec v w ∧ Rw [u] [w] [w])
          ∧ R u' v'

    def PointwiseMatchInductiveStep : Prop :=
      ∀ {u u' : S₁} {v : S₂} {w : W},
        R u v
        → u' = step impl u w
        → Rw [u] [w] [w]
          ∧ ∃ v', v' = step spec v w ∧ R u' v'

    theorem pointwise_implies_stuttering :
        PointwiseMatchInductiveStep impl spec R Rw
        → StutteringMatchInductiveStep impl spec R Rw := by
      introv ih _ hr hu'
      have ⟨hrw, v', _⟩ := ih hr hu'
      exists v' ; tauto

    def StutteringIndicator (stutter : S₁ → W → Bool) : Prop :=
      ∀ {u v} w,
        R u v → (R (step impl u w) (if stutter u w then v else (step spec v w)))
                ∧ (Rw [u] [w] (if stutter u w then [] else [w]))


    theorem stuttering_indicator_implies_stuttering
        {stutter : S₁ → W → Bool}
        (stutter_R : StutteringIndicator impl spec R Rw stutter) :
        StutteringMatchInductiveStep impl spec R Rw := by
      intro u u' v w hu hu' ; specialize stutter_R w hu
      split at stutter_R
      · exists v ; cc
      · exists (step spec v w) ; cc

    theorem stuttering_indicator_implies_must_issue [ComposableTraceRmap Rw]
        (isStalled : S₁ → Bool) (stutter_R : StutteringIndicator impl spec R Rw (fun u _ => isStalled u)) :
        MustIssueMatchInductiveStep impl spec R Rw isStalled := by
      intros u u' v trw tru w hr hstall htrw hfirst ; simp at *
      have hu := stutter_R w hr ; simp [hstall] at hu ; clear hstall hr
      rw [←List.append_nil [w], ←@List.singleton_append _ u, ←@List.singleton_append _ w]
      apply And.imp_left ComposableTraceRmap.Rw_compose.mp
      simp [hu.2] ; apply And.left at hu
      let ⟨v', hv'⟩ : ∃ v', v' = step spec v w := ⟨_, rfl⟩ ; rw [←hv'] at hu ; rw [←hv'] ; clear hv' v
      induction tru generalizing trw u w <;> simp at htrw
      · cases htrw ; subst trw u' ; simp [hu, ComposableTraceRmap.Rw_init]
      · rename_i u'' tru ih ; cases' htrw with hu'' htrw
        rw [←hu''] at hu ; clear u hu'' ; simp at hfirst
        cases trw ; simp at htrw
        rename_i w trw ;
        specialize stutter_R w hu ; simp [hfirst.1] at stutter_R
        specialize ih htrw hfirst.2 stutter_R.1
        have hRw := ComposableTraceRmap.Rw_compose.mp (And.intro stutter_R.2 ih.1)
        simp at hRw ; exact And.intro hRw ih.2

    theorem list_get_last {α} (xs : List α) :
        xs = [] ∨ ∃ xs' x, xs = xs' ++ [x] := by
      induction xs <;> simp
      rename_i x₁ xs ih ; cases xs <;> simp at *
      · exists [], x₁
      · let ⟨xs', x₂, _⟩ := ih
        exists (x₁ :: xs'), x₂ ; simp [*]

    theorem must_issue_implies_flush_point [ComposableTraceRmap Rw] {isStalled isFlushed} :
        (∀ s, isFlushed s → ! isStalled s)
        → MustIssueMatchInductiveStep impl spec R Rw isStalled
        → FlushPointMatchInductiveStep impl spec R Rw isFlushed := by
      intros hstall hmi u u' v trw tru hr hvalid hsu hsu'
      apply hstall at hsu ; apply hstall at hsu'
      unfold MustIssueMatchInductiveStep at hmi
      let ⟨n, hn⟩ : ∃ n, (tru ++ [u']).length ≤ n := ⟨_, le_rfl⟩
      induction n generalizing u v trw tru <;> simp at *
      rename_i n ih
      have hstru : ∃ u ∈ (tru ++ [u']), !isStalled u := ⟨u', by simp [hsu']⟩
      let ⟨tru₁, truRest, htrus, hfirst⟩ := TraceToFirst.trace_to_first hstru ; clear hstru
      apply Or.elim (list_get_last truRest)
      · intro htruRest ; subst truRest
        simp at htrus ; subst htrus
        cases trw ; simp at hvalid ; rename_i w trw
        specialize hmi hr hsu hvalid hfirst
        exists [w] ; simp [hmi.1]
        exists [], (step spec v w)
        apply And.intro <;> simp [*]
      · intro ⟨tru₂, _, _⟩ ; subst truRest
        rw [←List.append_assoc] at htrus
        apply List.append_inj_left' at htrus
        simp at htrus ; subst tru
        let ⟨tru₁, u'', htru₁, hu'', _⟩ := TraceToFirst.TraceToFirst_last.mp hfirst
        subst htru₁
        rw [List.append_assoc] at hvalid
        apply valid_run_append.mp at hvalid
        let ⟨trw₁, trw₂, htrw, hvalid₁, hvalid₂⟩ := hvalid ; clear hvalid
        cases trw₁ ; simp at hvalid₁ ; rename_i w trw₁
        simp at *
        specialize hmi hr hsu hvalid₁ hfirst
        specialize ih hmi.2 hvalid₂ hu'' (by omega)
        let ⟨trx, hrw, trv, v', hvalid, hr'⟩ := ih ; clear ih
        exists (w :: trx) ; apply And.intro
        · have hc := ComposableTraceRmap.Rw_compose.mp (And.intro hmi.1 hrw)
          rw [htrw] ; exact hc
        · exists step spec v w :: trv, v' ; simp [*]
  end Alignment

end TransitionSystems
