-- basic formula for unimodal logic
inductive formula 
| bottom        : formula 
| propositional : string → formula
| negation      : formula → formula
| diamond       : formula → formula
| disjunction   : formula → formula → formula

#check formula.diamond $ formula.negation $ formula.propositional "p"

-- equivalence
def box : formula → formula
:= formula.negation ∘ formula.diamond ∘ formula.negation

def conjunction : formula → formula → formula
| f g := formula.negation $ formula.disjunction (formula.negation f) (formula.negation g)

def implication : formula → formula → formula
| φ ψ := formula.disjunction ψ (formula.negation φ)

-- TODO: fix formatting of more complex formulas using parens
def formula.repr : formula → string
| (formula.negation (formula.diamond (formula.negation ψ))) := "□" ++ formula.repr ψ
| (formula.negation (formula.disjunction (formula.negation ψ) (formula.negation χ))) := formula.repr ψ ++ " ∧ " ++ formula.repr χ
| (formula.disjunction χ (formula.negation ψ)) := formula.repr ψ ++ " → " ++ formula.repr χ
| (formula.disjunction (formula.negation ψ) χ) := formula.repr ψ ++ " → " ++ formula.repr χ
| formula.bottom := "⊥"
| (formula.propositional s) := s
| (formula.negation ψ) := "¬" ++ formula.repr ψ
| (formula.diamond ψ) := "⋄" ++ formula.repr ψ
| (formula.disjunction ψ χ) := formula.repr ψ ++ " ∨ " ++ formula.repr χ

instance : has_repr formula := ⟨formula.repr⟩

def Frame (α : Type) := set (α × α)
    -- TODO: for now, let's try to take the worlds all values in set α. this is general enough in principle (we can always take subtypes)

def Valuation (α : Type) := string → set α

def pairs {α β : Type} (A : set α) (B: set β) : set (α × β) := { x | x.1 ∈ A ∧ x.2 ∈ B }

structure Model (α : Type) :=
    (frame : set (α × α)) -- TODO: use frame, but need to implement has_mem for it
    (valuation : Valuation α)

def satisfies {α : Type} (m : Model α) : α → formula → Prop
| _ formula.bottom            := false
| w (formula.negation f)      := ¬ (satisfies w f)
| w (formula.disjunction f g) := (satisfies w f) ∨ (satisfies w g)
| w (formula.propositional p) := w ∈ m.valuation p
| w (formula.diamond f)       := ∃ v : α, ((w, v) ∈ m.frame ∧ satisfies v f)

infixl `⊢` : 50    := function.uncurry satisfies

def validates {α : Type} : set (α × α) → formula → Prop
| 𝔽 φ := ∀ (V : Valuation α) (w : α), ({frame := 𝔽, valuation := V}, w) ⊢ φ

-- some shorthand
notation `□`       := box
notation `⋄`       := formula.diamond
notation `!`       := formula.negation -- ¬ would be nicer, but overloading is not allowed
notation `⟦` p `⟧` := formula.propositional p
infixr ` => ` : 10 := implication
infixl ` | ` : 40  := formula.disjunction
infixl ` & ` : 50  := conjunction
notation `⊥`       := formula.bottom
infixl `⊨` : 50    := validates

#check function.uncurry
#check (⊢)

#eval (□⟦"p"⟧ => !⟦"p"⟧).repr -- □p → ¬p

example {α : Type} (𝔽 : set (α × α)) (w : α) : ¬ 𝔽 ⊨ ⊥ := sorry

def Id (α : Type) : set (α × α) := { x | x.2 = x.1 }

def successors {α : Type} (r : set (α × α)) (w : α) : set α :=
    { x | (w, x) ∈ r }

def custom_val {α : Type} (𝔽 : set (α × α)) (w : α) (s : string) : set α :=
    successors 𝔽 w

lemma contrapositive {A B : Prop} (h : A → B) : ¬ B → ¬ A :=
begin
    intros h2 ha,
    have uh_oh := h ha,
    contradiction
end

lemma validate_4_iff_refl {α : Type} (𝔽 : set (α × α)) (p : string) :
    Id α ⊆ 𝔽 ↔ 𝔽 ⊨ (□⟦p⟧ => ⟦p⟧) :=
begin
    apply iff.intro,
    {
        intros h V w,
        cases classical.em (w ∈ V p),
        {
            exact or.inl h_1
        },
        {
            apply or.inr,
            intro h2,
            exact h2 ⟨w, by { apply h, exact rfl }, h_1⟩
        }
    },
    {
        intros val r h2,
        cases r,
        cases h2,
        -- TODO: see if we can do this w/o contradiction
        apply classical.by_contradiction,
        have neighbour_iff_in_val : ∀ x : α, (r_fst, x) ∈ 𝔽 ↔ x ∈ custom_val 𝔽 r_fst p := (λ x, by refl),
        specialize val (custom_val 𝔽 r_fst) r_fst,
        cases val,
        {
            have oh_no := iff.elim_right (neighbour_iff_in_val r_fst) val,
            contradiction
        },
        {
            cases classical.by_contradiction val,
            cases h,
            have oh_no := contrapositive (iff.elim_left (neighbour_iff_in_val w)) h_right,
            contradiction
        }        
    }
end

def bisimulation {α β : Type} (Z : set (α × β)) (m : Model α) (k : Model β) :=
    (∀ prop (z : α × β), z ∈ Z → (z.1 ∈ (m.valuation prop) ↔ z.2 ∈ (k.valuation prop))) -- valuation invariance
  ∧ (∀ (z : α × β), z ∈ Z → (∀ a', (z.1, a') ∈ m.frame → ∃ b', (z.2, b') ∈ k.frame ∧ (a', b') ∈ Z)) -- ZIG
  ∧ (∀ (z : α × β), z ∈ Z → (∀ b', (z.2, b') ∈ k.frame → ∃ a', (z.1, a') ∈ m.frame ∧ (a', b') ∈ Z)) -- ZAG

lemma bisimulation_preserves_satisfaction {α β : Type} {m : Model α} {m' : Model β} {w : α} {w' : β} (Z : set (α × β)) (h₂ : bisimulation Z m m') (h₁ : (w, w') ∈ Z):
    ∀ φ, (m, w) ⊢ φ ↔ (m', w') ⊢ φ :=
begin
    intro φ,
    cases h₂, -- TODO: rename these hypothesis to something more meaningful
    cases h₂_right,
    induction φ generalizing w w',
    {
        apply iff.intro; intro sat; cases sat
    },
    {
        exact ⟨assume sat, iff.elim_left (h₂_left φ (w, w') h₁) sat,
               assume sat, iff.elim_right (h₂_left φ (w, w') h₁) sat⟩
    },
    {
        exact ⟨assume sat, contrapositive (iff.elim_right (φ_ih h₁)) sat,
               assume sat, contrapositive (iff.elim_left (φ_ih h₁)) sat⟩
    },
    {
        -- okay this is the interesting part
        -- TODO: simplify! split to lemma?
        apply iff.intro; intro sat; cases sat; cases sat_h,
        {
            -- need forth condition
            have cond := h₂_right_left,
            specialize cond (w, w') h₁ sat_w sat_h_left,
            cases cond,
            cases cond_h,
            -- (sat_w, cond_w) is our new pair
            specialize φ_ih cond_h_right,
            apply exists.intro cond_w,
            exact ⟨ cond_h_left, iff.elim_left φ_ih sat_h_right ⟩
        },
        {
            -- need back condition
            have cond := h₂_right_right,
            specialize cond (w, w') h₁ sat_w sat_h_left,
            cases cond,
            cases cond_h,
            -- (cond_w, sat_w) is our new pair
            specialize φ_ih cond_h_right,
            apply exists.intro cond_w,
            exact ⟨ cond_h_left, iff.elim_right φ_ih sat_h_right ⟩
        }
    },
    {
        apply iff.intro; intro sat; cases sat,
        exact or.inl (iff.elim_left (φ_ih_a h₁) sat),
        exact or.inr (iff.elim_left (φ_ih_a_1 h₁) sat),
        exact or.inl (iff.elim_right (φ_ih_a h₁) sat),
        exact or.inr (iff.elim_right (φ_ih_a_1 h₁) sat)
    }
end

def bounded_morphism {α β} (f : α → β) (𝔽 : set (α × α)) (ℍ : set (β × β)) :=
    (∀ (r : α × α), r ∈ 𝔽 → (f(r.1), f(r.2)) ∈ ℍ) -- ZIG
  ∧ (∀ (r' : β × β), r' ∈ ℍ → ∀ a, f a = r'.1 → ∃ a', (a, a') ∈ 𝔽 ∧ f a' = r'.2) -- ZAG

-- AKA surjection
def onto {α β} (f : α → β) := ∀ b, ∃ a, f(a) = b

def func_as_set {α β} (f : α → β) : set (α × β) := { x | x.2 = f(x.1) }

example {α β} (a : α) (f : α → β) : (a, f a) ∈ func_as_set f := begin
    exact rfl
end

def custom_rel {α β} (f : α → β) (V' : string → set β) : string → set α := λ prop, { x | f x ∈ V' prop }

lemma bounded_morphic_img_preserves_validity {α β : Type} (𝔽 : set (α × α)) (ℍ : set (β × β)) (f : α → β) (h₁ : bounded_morphism f 𝔽 ℍ) (h₂ : onto f) :
    ∀ φ, 𝔽 ⊨ φ ↔ ℍ ⊨ φ :=
begin
    intro φ,
    apply iff.intro,
    {
        intro sat,
        intros V' w',
        specialize h₂ w',
        cases h₂,
        cases h₁,
        --rel = func_as_set f
        --V = custom_rel f V' = λ prop, { x | f x ∈ V' prop }
        have related_w_w' : (h₂_w, w') ∈ func_as_set f := begin
            rw ←h₂_h,
            exact rfl
        end,
        -- TODO: this should be a lemma
        have bisim : bisimulation (func_as_set f) ({frame := 𝔽, valuation := custom_rel f V'}) ({frame := ℍ, valuation := V'}) := begin
            apply and.intro,
            {
                -- prove that our new valuation works
                intros prop z z_in_rel,
                change z.snd = f z.fst at z_in_rel,
                apply iff.intro,
                {
                    intro z_fst_in_V,
                    change f z.fst ∈ V' prop at z_fst_in_V,
                    rw ←z_in_rel at z_fst_in_V,
                    assumption
                },
                {
                    intro z_snd_in_V',
                    change f z.fst ∈ V' prop,
                    rw z_in_rel at z_snd_in_V',
                    assumption
                }
            },
            {
                -- translating ZIG and ZAG properties
                apply and.intro,
                {
                    intros z z_in_rel a' 𝔽_neighbour,
                    specialize h₁_left (z.fst, a') 𝔽_neighbour,
                    change z.snd = f z.fst at z_in_rel,
                    rw z_in_rel,
                    exact exists.intro (f a') (and.intro h₁_left rfl)
                },
                {
                    intros z z_in_rel b' ℍ_neighbour,
                    specialize h₁_right (z.snd, b') ℍ_neighbour z.fst (eq.symm z_in_rel),
                    cases h₁_right,
                    cases h₁_right_h,
                    exact exists.intro h₁_right_w ⟨h₁_right_h_left, eq.symm h₁_right_h_right⟩
                }
            }
        end,
        -- use bisimulation result
        exact iff.elim_left (bisimulation_preserves_satisfaction (func_as_set f) bisim related_w_w' φ) (sat (custom_rel f V') h₂_w)
    },
    {
        sorry -- exactly as the other case, maybe even simpler
    }
end
