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

-- todo write a nice string representation

def Frame (α : Type) := set (α × α)
    -- TODO: for now, let's try to take the worlds all values in set α. this is general enough in principle (we can always take subtypes)

def Valuation (α : Type) := string → set α

structure Model (α : Type) :=
    (frame : set (α × α)) -- TODO: use frame, but need to implement has_mem for it
    (valuation : Valuation α)

def satisfies {α : Type} (m : Model α) : formula → α → Prop
| formula.bottom _            := false
| (formula.negation f) w      := ¬ (satisfies f w)
| (formula.disjunction f g) w := (satisfies f w) ∨ (satisfies g w)
| (formula.propositional p) w := w ∈ m.valuation p
| (formula.diamond f) w       := ∃ v : α, ((w, v) ∈ m.frame ∧ satisfies f v)

def validates {α : Type} : formula → set (α × α) → Prop
| φ 𝔽 := ∀ (V : Valuation α) (w : α), satisfies {frame := 𝔽, valuation := V} φ w

-- some shorthand
notation `⊞`       := box
notation `⋄`       := formula.diamond
notation `!`       := formula.notation -- ¬ would be nicer, but overloading is not allowed
notation `⟦` p `⟧` := formula.propositional p
infixr ` => ` : 90 := implication
infixl ` | ` : 40  := formula.disjunction
infixl ` & ` : 50  := conjunction
notation `⊥`       := formula.bottom

def Id (α : Type) : set (α × α) := { x | x.2 = x.1 }

def successors {α : Type} (r : set (α × α)) (w : α) : set α :=
    { x | (w, x) ∈ r }

lemma validate_4_iff_refl {α : Type} (𝔽 : set (α × α)) (p : string) : Id α ⊆ 𝔽 ↔ validates (⊞⟦p⟧ => ⟦p⟧) 𝔽 :=
begin
    simp [box, satisfies],
    apply iff.intro,
    {
        intros h V w,
        simp [implication, satisfies],
        cases classical.em (w ∈ V p), -- can we do w/o this?
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
        -- we could have a valuation only for p, but it doesnt matter
        have custom_val : string → set α := (λ prop, successors 𝔽 r_fst),
        specialize val custom_val r_fst,
        simp [implication, satisfies] at val,
        cases val,
        {
            intro h3,
            have r_fst_refl : (r_fst, r_fst) ∈ 𝔽 ↔ r_fst ∈ custom_val p := sorry, -- wish we could 'by refl' this
            have oh_no := iff.elim_right r_fst_refl val,
            contradiction
        },
        {
            have yolo : ∃ (v : α), (r_fst, v) ∈ 𝔽 ∧ v ∉ custom_val p :=
                begin
                    apply classical.by_contradiction,
                    apply val,
                end,
            cases yolo,
            cases yolo_h,
            intro unimportant,
            have swag : yolo_w ∉ custom_val p ↔ (r_fst, yolo_w) ∉ 𝔽 := sorry,
            -- we could probably generalize the above statement
            have oh_no := iff.elim_left swag yolo_h_right,
            contradiction
        }        
    }
end
