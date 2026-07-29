import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
open List

set_option linter.style.longLine false

abbrev TypeVar := Int

inductive T
  | Var : TypeVar → T
  | To : T → T → T
  deriving BEq
local infixr:50 " to " => T.To

inductive Λₜ
  | Var : TypeVar → Λₜ
  | Appl : Λₜ → Λₜ → Λₜ
  | Abst : TypeVar → T → Λₜ → Λₜ
local infixl:50 " $ " => Λₜ.Appl

def FV (M : Λₜ) : Set TypeVar :=
  match M with
  | Λₜ.Var v => {v}
  | Λₜ.Appl L N => FV L ∪ FV N
  | Λₜ.Abst x _ m => FV m \ {x}

def BV (M : Λₜ) : Set TypeVar :=
  match M with
  | Λₜ.Abst x _ m => {x} ∪ BV m
  | Λₜ.Var _ => {}
  | Λₜ.Appl L N => BV L ∪ BV N

abbrev Declaration : Type := Prod TypeVar T

abbrev Statement : Type := Prod Λₜ T

-- assuming all subjects are distinct
abbrev Context : Type := Set Declaration

set_option linter.style.dollarSyntax false
inductive Judgement : Context → Λₜ → T → Prop
  | Var {context : Context} {x : TypeVar} {t : T} (hx : ⟨x,t⟩ ∈ context) : Judgement context (Λₜ.Var x) t
  | Appl {context : Context} {σ τ : T} {M N : Λₜ} (hm : Judgement context M (σ to τ)) (hn : Judgement context N σ) : Judgement context (M $ N) τ
  | Abst {context : Context} {x : TypeVar} {σ τ : T} {M : Λₜ} (hx : ⟨x,σ⟩ ∈ context) (hm : Judgement context M τ) : Judgement (context \ {⟨x,σ⟩}) (Λₜ.Abst x σ M) (σ to τ)
abbrev J := Judgement

def Legal (M : Λₜ) : Prop :=
  ∃ context : Context, ∃ ρ : T, Judgement context M ρ

def dom (set : Context) : Set TypeVar :=
  Set.image (fun p => p.fst) set

def Subcontext (Γ' Γ : Context) : Prop := Γ' ⊆ Γ

def projection (Γ : Context) (Φ : Set TypeVar) : Context :=
  {p ∈ Γ | p.fst ∈ Φ}

theorem FreeVarLemma : Judgement Γ M t → FV M ⊆ dom Γ := by
  intro judgement
  induction judgement
  · rename_i hx
    rw [Set.subset_def]
    unfold FV dom
    intro x hxx
    simp?
    apply Exists.intro; apply And.intro hx
    simp?
    exact Eq.symm (Set.eq_of_mem_singleton hxx)
  · rename_i context σ τ M N hm hn hm_ih hn_ih
    rw [Set.subset_def]
    intro x hx
    unfold FV at hx
    rw [Set.subset_def] at hm_ih hn_ih
    cases hx with
    | inl hl => exact hm_ih x hl
    | inr hr => exact hn_ih x hr
  · rename_i context x σ τ M hx hm hm_ih
    rw [Set.subset_def] at *
    intro x hx
    unfold FV at hx
    simp? at hx
    unfold dom at *
    simp? at *
    have := hm_ih x hx.left
    have : ∃ t : T, ⟨x,t⟩ ∈ context.context := by
      apply Exists.elim this
      exact (fun w => fun hw => by
                apply Exists.intro w.snd
                rw [Eq.symm hw.right]
                exact hw.left)
    apply Exists.elim this
    exact (fun t => fun ht => by
                apply Exists.intro ⟨x,t⟩
                apply And.intro
                · apply And.intro
                  · exact ht
                  · intro heq
                    injection heq
                    rename_i snd_eq fst_eq
                    exact hx.right snd_eq
                · simp?)

lemma Generation_Var (judgement : Judgement Γ (Λₜ.Var x) σ) : ⟨x,σ⟩ ∈ Γ := by
  cases judgement with
  | Var hx => exact hx

lemma Generation_Appl (judgement : Judgement Γ (Λₜ.Appl M N) τ)
  : ∃ σ : T, Judgement Γ M (σ to τ) ∧ Judgement Γ N σ := by
    cases judgement with
    | Appl hm hn =>
      rename_i σ'
      apply Exists.intro σ'
      exact And.intro hm hn

lemma Generation_Abst (judgement : Judgement Γ (Λₜ.Abst x σ M) ρ)
  : ∃ τ : T, ((Judgement (Γ ∪ {⟨x,σ⟩}) M τ) ∧ (ρ = T.To σ τ)) := by
    cases judgement with
    | Abst hx hm =>
        rename_i context τ'
        have : context \ {⟨x,σ⟩} ∪ {⟨x,σ⟩} = context := by
          ext y
          constructor
          · rintro (⟨hy, _⟩ | rfl)
            · exact hy
            · exact hx
          · intro hy
            by_cases h_eq : y = ⟨x, σ⟩
            · right
              exact h_eq
            · left
              exact ⟨hy, h_eq⟩
        apply Exists.intro τ'
        rw [this]
        apply And.intro
        · exact hm
        · rfl

theorem Thinning : ∀ Γ' Γ'' : Context, ∀ M : Λₜ, ∀ σ : T, Γ' ⊆ Γ'' → Judgement Γ' M σ → Judgement Γ'' M σ := by
  intro Γ' Γ'' M σ hg judgement
  induction M generalizing Γ' Γ'' σ with
  | Var x =>
    have : ⟨x,σ⟩ ∈ Γ' := Generation_Var judgement
    rw [Set.subset_def] at hg
    apply Judgement.Var
    exact hg ⟨x,σ⟩ this
  | Appl M N ih1 ih2 =>
    have := Generation_Appl judgement
    apply Exists.elim this
    intro τ htau
    have a1 := ih1 Γ' Γ'' (τ to σ) hg htau.left
    have a2 := ih2 Γ' Γ'' τ hg htau.right
    exact Judgement.Appl a1 a2
  | Abst x ρ M ih =>
    have := Generation_Abst judgement
    apply Exists.elim this
    intro τ htau
    have : Γ' ∪ {⟨x,ρ⟩} ⊆ Γ'' ∪ {⟨x,ρ⟩} := by
      rw [Set.subset_def] at *
      intro w hw
      cases hw with
      | inl hwl => exact Or.inl (hg w hwl)
      | inr hwr => exact Or.inr hwr
    have ihj := ih (Γ' ∪ {⟨x,ρ⟩}) (Γ'' ∪ {⟨x,ρ⟩}) τ this htau.left
    have : ⟨x,ρ⟩ ∈ Γ'' ∪ {⟨x,ρ⟩} := by simp?
    have := Judgement.Abst this ihj
    rw [htau.right]
    sorry
