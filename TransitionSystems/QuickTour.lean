import Mathlib.Data.BitVec


/-
  A quick tour of Lean
  1. Lean as a programming language
  2. Example transition systems + proofs about them
  3. Formalizing your meta-theory in Lean
     (e.g., for transition systems)
-/



namespace Temp

  #check 3#5
  #eval 3#5

  def x : BitVec 5 := 4#5
  #eval x + 2#5
  #eval x + 2#4
  -- type error, can't add bitvecs of different size

  def add_twice (a b : BitVec 32) := a + b + b

  #eval add_twice 2#32 5#32

end Temp





structure SpecState where
  x : BitVec 32
  deriving Repr  -- makes SpecState printable


namespace Temp

  def specStart : SpecState := { x := 1#32 }
  #eval specStart

  def specStep (u : SpecState) : SpecState :=
      { x := BitVec.shiftLeft u.x 1 }

  #check BitVec.shiftLeft

  #eval specStep specStart
  #eval specStep (specStep specStart)
  #eval specStep (specStep (specStep specStart))





  namespace stepK

    def specStepK (u : SpecState) (k : ℕ) :=
      if k = 0 then u
      else specStepK (specStep u) (k - 1)

    #eval specStepK specStart 3


    def specStepK' (u : SpecState) : ℕ → SpecState
    | 0 => u
    | (k + 1) => specStepK' (specStep u) k

    #eval specStepK' specStart 3


    -- In Lean, recursive functions must
    -- provably terminate
    def specStepK'' (u : SpecState) : ℕ → SpecState
    | 0 => u
    | k => specStepK'' (specStep u) (k - 1)
    termination_by k => k
    decreasing_by sorry
    /- Here, the pattern of the second branch
       also accepts k=0, making it difficult to
       infer/prove termination. --/

  end stepK


  def specStepK := stepK.specStepK'


  theorem spec_step_k_0 :
      ∀ u, specStepK u 0 = u := by
    intro u
    unfold specStepK
    unfold stepK.specStepK'
    rfl


  theorem spec_step_k_0' :
      ∀ u, specStepK u 0 = u := by
    intro u ; rfl


  theorem spec_step_k_0'' :
      ∀ u, specStepK u 0 = u :=
    fun _ => rfl

  theorem spec_step_k_step : ∀ u k,
      specStepK u (k + 1)
      = specStepK (specStep u) k :=
    fun _ _ => rfl


  -- what if we unroll steps from the other side?
  theorem spec_step_step_k : ∀ u k,
      specStepK u (k + 1)
      = specStep (specStepK u k) := by
    introv
    induction k generalizing u
    · rfl
    · rename_i k ih
      rw [spec_step_k_step,
          ih,
          spec_step_k_step]




  -- Group exercise:
  theorem spec_is_correct_sorry : ∀ k,
      (specStepK specStart k).x
       = (1#32).shiftLeft k := by
    sorry
















  -- Where we get stuck:
  theorem spec_is_correct_sorry' : ∀ k,
      (specStepK specStart k).x
      = (1#32).shiftLeft k := by
    intro k
    induction k
    case zero => rw [spec_step_k_0]
                 rfl
    case succ k ih =>
      rw [spec_step_k_step] ; sorry














  theorem spec_is_correct_helper : ∀ u k,
      (specStepK u k).x = u.x.shiftLeft k := by
    intro u k
    induction k generalizing u
    case zero => rw [spec_step_k_0,
                     BitVec.shiftLeft_eq,
                     BitVec.shiftLeft_zero_eq]
    case succ k ih =>
      rw [spec_step_k_step, ih]
      unfold specStep ; simp
      /- `simp` is a wonderful tactic that
          simplifies the proof goal based on
          a database of lemmas. -/
      rw [Nat.add_comm, BitVec.shiftLeft_add]


  theorem spec_is_correct : ∀ k,
      (specStepK specStart k).x
      = (1#32).shiftLeft k := by
    apply spec_is_correct_helper
    -- exact spec_is_correct_helper specStart
    -- exact spec_is_correct_helper _

end Temp










structure ImplState where
  state : BitVec 1
  x : BitVec 32
  y : BitVec 32
  deriving Repr


namespace Temp

  def implStart : ImplState := {
    state := 0#1
    x := 1#32
    y := 1#32
  }

  def implStep (v : ImplState) : ImplState :=
    if v.state = 0#1
    then { state := 1#1, x := v.x, y := v.x }
    else { state := 0#1, x := v.x + v.y, y := v.y }

  def implStepK (v : ImplState) : ℕ → ImplState
  | 0 => v
  | k + 1 => implStepK (implStep v) k

  #eval implStepK implStart 1
  #eval implStepK implStart 2
  #eval implStepK implStart 4
  #eval implStepK implStart 6


  /- Lean has powerful inference. Here we tell it
     to infer the value of `v` whenever the
     theorem is used. -/
  theorem impl_step_k_0 :
    ∀ {v}, implStepK v 0 = v := rfl

  theorem impl_step_k_step : ∀ {v k},
      implStepK v (k + 1)
      = implStepK (implStep v) k := rfl

  theorem impl_step_step_k : ∀ {v k},
      implStepK v (k + 1)
      = implStep (implStepK v k) := by
    introv ; induction k generalizing v
    · rfl
    · rename_i k ih
      rw [impl_step_k_step, ih, impl_step_k_step]


  /- Lean has recently implemented decision
     procedures for bitvectors: -/
  theorem left_shift_one_32 : ∀ x : BitVec 32,
    x <<< 1 = x + x := by bv_decide


  theorem spec_simulates_impl_sorry : ∀ k₁ v,
      v = implStepK implStart k₁
      → ∃ k₂ u, u = specStepK specStart k₂
        ∧ u.x = v.x := by
    introv hv
    induction k₁ generalizing v
    -- Group Exercise (use sorry for vpre.state = 1#1)
    · sorry
    · sorry



















    -- · exists 0, specStart
    --   rw [spec_step_k_0, hv, impl_step_k_0]
    --   apply And.intro rfl rfl
    -- · rename_i k₁ ih
    --   rw [impl_step_impl_step_k] at hv
    --   set vpre := implStepK implStart k₁
    --   specialize ih vpre rfl
    --   let ⟨k₂, upre, hstepk₂, habs⟩ := ih ; clear ih
    --   unfold implStep at hv
    --   split at hv
    --   · exists k₂, upre ; simp [hv, habs]
    --     exact hstepk₂
    --   · sorry



    def spec_impl_abs_rel (u : SpecState) (v : ImplState) : Prop :=
      u.x = v.x ∧ (v.state = 1#1 → v.x = v.y)


    theorem spec_impl_commutating_diagram :
      ∀ {u : SpecState} {v : ImplState},
        spec_impl_abs_rel u v
        → v' = implStep v
        → ∃ u', (u' = u ∨ u' = specStep u)
              ∧ spec_impl_abs_rel u' v' := by
      intro u v ⟨habs, hstate⟩ hv
      unfold implStep at hv
      split at hv
      · exists u ; simp [*, spec_impl_abs_rel]
      · exists specStep u
        simp [spec_impl_abs_rel, specStep, *]
        bv_decide


    theorem spec_simulates_impl_helper : ∀ k₁ v,
      v = implStepK implStart k₁
      → ∃ k₂ u, u = specStepK specStart k₂
        ∧ spec_impl_abs_rel u v := by
    introv hv
    induction k₁ generalizing v
    · exists 0, specStart
      rw [spec_step_k_0, hv, impl_step_k_0]
      simp [spec_impl_abs_rel, specStart, implStart]
    · rename_i k₁ ih
      rw [impl_step_step_k] at hv
      set vpre := implStepK implStart k₁
      specialize ih vpre rfl
      let ⟨k₂, upre, hstepk₂, habs⟩ := ih ; clear ih
      let ⟨u', hu', habs'⟩ :=
        spec_impl_commutating_diagram habs hv
      cases hu'
      · subst u' ; exists k₂, upre
      · exists k₂ + 1, u'
        rw [spec_step_step_k, ←hstepk₂]
        apply And.intro <;> assumption


    theorem spec_simulates_impl : ∀ k₁ v,
        v = implStepK implStart k₁
        → ∃ k₂ u, u = specStepK specStart k₂
          ∧ u.x = v.x := by
      introv hv
      apply spec_simulates_impl_helper at hv
      let ⟨k₂, u, _, _, _⟩ := hv ; clear hv
      exists k₂, u

end Temp






/- Note the duplicated functions and theorems
   between impl and spec:
    implStepK, impl_step_k_0, impl_step_k_step,
    impl_step_step_k
  are very similar to
    specStepK, spec_step_k_0, spec_step_k_step,
    spec_step_step_k
-/

-- A general form of a transition system
structure TransitionSystem (S : Type) where
  start : S
  step : S → S


#check TransitionSystem.start
#check TransitionSystem.step



def spec : TransitionSystem SpecState := {
  start := { x := 1#32 }
  step := fun u => { x := u.x <<< 1 }
}

def impl : TransitionSystem ImplState := {
  start := { state := 0#1, x := 1#32, y := 1#32 },
  step := fun v =>
    if v.state = 0#1
    then { state := 1#1, x := v.x, y := v.x }
    else { state := 0#1, x := v.x + v.y, y := v.y }
}

#check spec.start
#check impl.step


namespace TransitionSystem


  -- Any transition system can take k steps
  def stepK {S} (m : TransitionSystem S) (s : S) : ℕ → S
  | 0 => s
  | k + 1 => stepK m (m.step s) k
  -- (Here we consider deterministic transition systems)

  /-
    Lean is based on the Calculus of Inductive Constructions.
    - types can depend on terms (dependent types)
    - terms can depend on types (polymorphism)
    - types can depend on types
  -/


  #check spec.stepK spec.start


  @[simp]
  theorem step_k_0 :
    ∀ {S} {m : TransitionSystem S} {s : S},
    m.stepK s 0 = s := rfl

  @[simp]
  theorem step_k_step :
    ∀ {S} {m : TransitionSystem S} {s : S},
    m.stepK s (k + 1) = m.stepK (m.step s) k := rfl

  theorem step_step_k :
      ∀ {S} {m : TransitionSystem S} {s : S},
      m.stepK s (k + 1) = m.step (m.stepK s k) := by
    introv ; induction k generalizing s
    · rfl
    · rename_i k ih ; simp [←ih]



  def StepsTo {S} (m : TransitionSystem S)
              (s s' : S) : Prop :=
    s' = m.step s


  notation s:arg " -[" m:arg "]-> " s':arg =>
    TransitionSystem.StepsTo m s s'


  theorem steps_to_next :
    spec.start -[ spec ]-> (spec.step spec.start) := by rfl


  def Reaches {S} (m : TransitionSystem S)
              (s s' : S) : Prop :=
    ∃ k, s' = m.stepK s k


  notation s:arg " -[" m:arg "]->* " s':arg =>
    TransitionSystem.Reaches m s s'



  theorem step_reaches {S} {m : TransitionSystem S} :
      ∀ {s s' s''},
      s -[m]-> s'
      → s' -[m]->* s''
      → s -[m]->* s'' := by
    simp [Reaches, StepsTo]
    intro s s' s'' hs' k hs''
    exists k + 1 ; rw [step_k_step, ←hs', ←hs'']



  theorem reaches_step {S} {m : TransitionSystem S} :
      ∀ {s s' s''},
      s -[m]->* s'
      → s' -[m]-> s''
      → s -[m]->* s'' := by
    simp [Reaches, StepsTo]
    intro s s' s'' k hs' hs''
    exists k + 1 ; rw [step_step_k, ←hs', ←hs'']



  def StutteringCommutativeDiagram {S T}
    (spec : TransitionSystem S)
    (impl : TransitionSystem T)
    (abs : S → T → Prop) : Prop :=
    ∀ {u : S} {v v' : T},
      abs u v
      → v -[impl]-> v'
      → ∃ u', (u = u' ∨ u -[spec]-> u')
              ∧ abs u' v'


  def Simulation {S T}
    (spec : TransitionSystem S)
    (impl : TransitionSystem T)
    (abs : S → T → Prop) :=
    ∀ (v' : T),
      impl.start -[impl]->* v'
      → ∃ u', spec.start -[spec]->* u' ∧ abs u' v'


  theorem simulation_via_stuttering_diagram :
    ∀ {S T}
      {spec : TransitionSystem S}
      {impl : TransitionSystem T}
      {abs : S → T → Prop},
      abs spec.start impl.start
      → StutteringCommutativeDiagram spec impl abs
      → Simulation spec impl abs := by
    introv hstart hdia v'
    intro ⟨k₁, hstepk₁⟩
    induction k₁ generalizing v'
    · exists spec.start
      subst v' ; simp [hstart] ; clear hstart
      exists 0
    · rename_i k₁ ih
      rw [step_step_k] at hstepk₁
      specialize ih (impl.stepK impl.start k₁) rfl
      set vpre := impl.stepK impl.start k₁
      let ⟨upre, hupre, habs⟩ := ih ; clear ih
      specialize hdia habs hstepk₁
      let ⟨u', hu', habs'⟩ := hdia ; clear hdia
      cases hu'
      · subst upre ; exists u'
      · exists u' ; simp [habs']
        apply reaches_step hupre ; assumption



end TransitionSystem
