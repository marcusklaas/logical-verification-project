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
| (formula.negation (formula.diamond (formula.negation ψ))) := "⊞" ++ formula.repr ψ
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

structure Model (α : Type) :=
    (frame : set (α × α)) -- TODO: use frame, but need to implement has_mem for it
    (valuation : Valuation α)

def satisfies {α : Type} (m : Model α) : α → formula → Prop
| _ formula.bottom            := false
| w (formula.negation f)      := ¬ (satisfies w f)
| w (formula.disjunction f g) := (satisfies w f) ∨ (satisfies w g)
| w (formula.propositional p) := w ∈ m.valuation p
| w (formula.diamond f)       := ∃ v : α, ((w, v) ∈ m.frame ∧ satisfies v f)

def validates {α : Type} : set (α × α) → formula → Prop
| 𝔽 φ := ∀ (V : Valuation α) (w : α), satisfies {frame := 𝔽, valuation := V} w φ

-- some shorthand
notation `⊞`       := box
notation `⋄`       := formula.diamond
notation `!`       := formula.negation -- ¬ would be nicer, but overloading is not allowed
notation `⟦` p `⟧` := formula.propositional p
infixr ` => ` : 10 := implication
infixl ` | ` : 40  := formula.disjunction
infixl ` & ` : 50  := conjunction
notation `⊥`       := formula.bottom
infixl `⊨` : 50    := validates
-- notation `(` 𝔽`,` w `)` `⊢` φ := satisfies 𝔽 w φ

#eval (⊞⟦"p"⟧ => !⟦"p"⟧).repr -- ⊞p → ¬p

example {α : Type} (𝔽 : set (α × α)) (w : α) : ¬ 𝔽 ⊨ ⊥ := sorry

def Id (α : Type) : set (α × α) := { x | x.2 = x.1 }

def successors {α : Type} (r : set (α × α)) (w : α) : set α :=
    { x | (w, x) ∈ r }

def custom_val {α : Type} (𝔽 : set (α × α)) (w : α) (s : string) : set α :=
    successors 𝔽 w

lemma contrapositive (A B : Prop) (h : A → B) : ¬ B → ¬ A :=
begin
    intros h2 ha,
    have uh_oh := h ha,
    contradiction
end

lemma validate_4_iff_refl {α : Type} (𝔽 : set (α × α)) (p : string) :
    Id α ⊆ 𝔽 ↔ 𝔽 ⊨ (⊞⟦p⟧ => ⟦p⟧) :=
begin
    simp [box, satisfies],
    apply iff.intro,
    {
        intros h V w,
        simp [implication, satisfies],
        cases classical.em (w ∈ V p),
        {
            exact or.inl h_1
        },
        {
            apply or.inr,
            intro h2,
            apply h2,
            apply exists.intro w,
            apply and.intro,
            {
                apply h,
                exact rfl
            },
            {
                assumption
            }
        }
    },
    {
        intros val r h2,
        cases r,
        cases h2,
        apply classical.by_contradiction,
        simp [validates] at val,
        have neighbour_iff_in_val : ∀ x : α, (r_fst, x) ∈ 𝔽 ↔ x ∈ custom_val 𝔽 r_fst p := begin
            intro x,
            refl
        end,
        specialize val (custom_val 𝔽 r_fst) r_fst,
        simp [implication, satisfies] at val,
        cases val,
        {
            intro h3,
            have oh_no := iff.elim_right (neighbour_iff_in_val r_fst) val,
            contradiction
        },
        {
            have yolo : ∃ (v : α), (r_fst, v) ∈ 𝔽 ∧ v ∉ custom_val 𝔽 r_fst p :=
                begin
                    apply classical.by_contradiction,
                    apply val,
                end,
            cases yolo,
            cases yolo_h,
            intro unimportant,
            have swag : yolo_w ∉ custom_val 𝔽 r_fst p → (r_fst, yolo_w) ∉ 𝔽 := begin
                apply contrapositive,
                exact iff.elim_left (neighbour_iff_in_val yolo_w),
            end,
            have oh_no := swag yolo_h_right,
            contradiction
        }        
    }
end
