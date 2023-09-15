import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.Util.AtomM

set_option autoImplicit true

namespace Mathlib.Tactic.Bicategory

open Mathlib.Meta Qq NormNum Lean.Meta AtomM Lean.Elab
open Lean (MetaM Expr mkRawNatLit)
open Lean.Elab.Tactic
open CategoryTheory
-- open Lean

#check @Bicategory.whiskerRight
#check FreeBicategory.of.obj
#check Prefunctor.obj

#check Lean.ToExpr.toExpr

open Lean Elab Meta Tactic

structure Context where
  /-- The type of the ambient bicategory. -/
  B       : Expr
  /-- The universe level for objects. -/
  univObj    : Level
  /-- The universe level for morphisms. -/
  univHom    : Level
  /-- The universe level for 2-morphisms. -/
  univHom₂    : Level
  /-- The `Bicategory B`. -/
  inst    : Expr

abbrev M := ReaderT Context TermElabM

def Context.app (c : Context) (n : Name) (inst : Expr) : Array Expr → Expr :=
  mkAppN (((Expr.const n [c.univHom₂, c.univHom, c.univObj]).app c.B).app inst)

def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app n c.inst xs

#check FreeBicategory.of
#check Prefunctor.map
#check Bicategory.toCategoryStruct.toQuiver

universe w v u

def _root_.CategoryTheory.FreeBicategory.of' (B : Type u) [Bicategory.{w, v} B] :
    Prefunctor B (FreeBicategory B) :=
  FreeBicategory.of

-- -- set_option quotPrecheck false in
-- partial def free₁ (e : Expr) : TermElabM Expr := do
--   -- let els := do
--   --   pure (q(FreeBicategory.of.map $f) : Expr)
--   -- let .const n _ := e.getAppFn | els
--   -- let .const n _ := (← withReducible <| whnf e).getAppFn | throwError "error not const"
--   match e, e.getAppFnArgs with
--   | _, (``CategoryStruct.comp, #[_, _, _, _, _, f, g]) =>
--     mkAppM ``CategoryStruct.comp #[← free₁ f, ← free₁ g]
--   | _, (``CategoryStruct.id, #[_, _, a]) =>
--     -- mkAppM ``CategoryStruct.id #[← mkAppM ``Prefunctor.obj #[.const ``FreeBicategory.of [], a]]
--     Term.elabTerm (← `(CategoryStruct.id (FreeBicategory.of.obj $(← Term.exprToSyntax a)))) none
--   | f, _ =>
--     Term.elabTerm (← `(FreeBicategory.of.map $(← Term.exprToSyntax f))) none
--     -- IO.println (← f.)

#check Quiver.Hom

#check Command.liftTermElabM

#check @Bicategory.toCategoryStruct.2
#check @Bicategory.toCategoryStruct.3
#check CategoryStruct.id

-- partial def free₁ (e : Expr) : MetaM Expr := do
--   match ← whnfD e with
--   -- `comp`
--   | .proj ``CategoryStruct 2 e =>
--     mkAppM ``CategoryStruct.comp #[← free₁ f, ← free₁ g]
--   | (``CategoryStruct.id, #[a]) =>
--     let B ← inferType a
--     mkAppM ``CategoryStruct.id #[← mkAppM ``Prefunctor.obj
--       #[← mkAppOptM ``FreeBicategory.of #[B, none], a]]
--   -- | (``Bicategory.toCategoryStruct.2, #[]) =>
--   --   throwError ""
--   | (n, xs) =>
--     IO.println (n)
--     IO.println (xs)
--     IO.println <| (← whnfD e)
--     match (← inferType e).getAppFnArgs with
--     | (``Quiver.Hom, #[_, _, a, _]) =>
--       let B ← inferType a
--       mkAppM ``Prefunctor.map #[← mkAppOptM ``FreeBicategory.of #[B, none], e]
--     | _ => throwError "{e} is not a morphism"

partial def free₁ (e : Expr) : MetaM Expr := do
  -- let (e, _) ← dsimp e (← Simp.Context.ofNames)
  let (``Quiver.Hom, #[_, _, a, b]) := (← whnfR <| ← inferType e).getAppFnArgs
    | throwError "{e} is not a morphism"
  let c ← mkFreshExprMVar (← inferType a)
  let f ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[a, c])
  let g ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[c, b])
  if ← withDefault <| isDefEq e (← mkAppM ``CategoryStruct.comp #[f, g]) then
    mkAppM ``CategoryStruct.comp #[← free₁ f, ← free₁ g]
  else match (← whnfR e).getAppFnArgs with
    | (``CategoryStruct.id, #[_, _, a]) =>
      let B ← inferType a
      mkAppM ``CategoryStruct.id #[← mkAppM ``Prefunctor.obj
        #[← mkAppOptM ``FreeBicategory.of #[B, none], a]]
    | _ =>
      match (← inferType e).getAppFnArgs with
      | (``Quiver.Hom, #[_, _, a, _]) =>
        let B ← inferType a
        mkAppM ``Prefunctor.map #[← mkAppOptM ``FreeBicategory.of #[B, none], e]
      | _ => throwError "{e} is not a morphism"

-- partial def free₁ (e : Expr) : MetaM Expr := do
--   let (e, _) ← dsimp e (← Simp.Context.ofNames)
--   match (← whnfR e).getAppFnArgs with
--   | (``CategoryStruct.comp, #[_, _, _, _, _, f, g]) =>
--     mkAppM ``CategoryStruct.comp #[← free₁ f, ← free₁ g]
--   | (``CategoryStruct.id, #[_, _, a]) =>
--     let B ← inferType a
--     mkAppM ``CategoryStruct.id #[← mkAppM ``Prefunctor.obj
--       #[← mkAppOptM ``FreeBicategory.of #[B, none], a]]
--   -- | (``Bicategory.toCategoryStruct.2, #[]) =>
--   --   throwError ""
--   | _ =>
--     -- IO.println (n)
--     -- IO.println (xs)
--     -- IO.println <| (← whnfR e)
--     match (← inferType e).getAppFnArgs with
--     | (``Quiver.Hom, #[_, _, a, _]) =>
--       let B ← inferType a
--       mkAppM ``Prefunctor.map #[← mkAppOptM ``FreeBicategory.of #[B, none], e]
--     | _ => throwError "{e} is not a morphism"

partial def free₂ (e : Expr) : MetaM Expr := do
  let error : MetaM Expr := throwError "{← whnfR e} is not a structural 2-morphism"
  -- IO.println (← ppExpr <| (← whnfR e))
  match e.getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
    mkAppM ``CategoryStruct.comp #[← free₂ η, ← free₂ θ]
  | (``Bicategory.whiskerLeft, #[_, _, _, _, _, f, _, _, η]) =>
    mkAppM ``Bicategory.whiskerLeft #[← free₁ f, ← free₂ η]
  | (``Bicategory.whiskerRight, #[_, _, _, _, _, _, _, η, h]) =>
    mkAppM ``Bicategory.whiskerRight #[← free₂ η, ← free₁ h]
  | (``CategoryStruct.id, #[_, _, f]) =>
    mkAppM ``CategoryStruct.id #[← free₁ f]
  | (``Iso.hom, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
      mkAppM ``Iso.hom #[← mkAppM ``Bicategory.associator #[← free₁ f, ← free₁ g, ← free₁ h]]
    | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
      mkAppM ``Iso.hom #[← mkAppM ``Bicategory.leftUnitor #[← free₁ f]]
    | (``Bicategory.rightUnitor, #[_, _, _, _, f]) =>
      mkAppM ``Iso.hom #[← mkAppM ``Bicategory.rightUnitor #[← free₁ f]]
    | _ => throwError "{← whnf η} is not a structural 2-morphism"
  | (``Iso.inv, #[_, _, _, _, η]) =>
    match (← whnfR η).getAppFnArgs with
    | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
      mkAppM ``Iso.inv #[← mkAppM ``Bicategory.associator #[← free₁ f, ← free₁ g, ← free₁ h]]
    | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
      mkAppM ``Iso.inv #[← mkAppM ``Bicategory.leftUnitor #[← free₁ f]]
    | (``Bicategory.rightUnitor, #[_, _, _, _, f]) =>
      mkAppM ``Iso.inv #[← mkAppM ``Bicategory.rightUnitor #[← free₁ f]]
    | _ => error
  | _ => error

#check FreeBicategory.lift

#check Pseudofunctor.toPrelaxFunctor
#check PrelaxFunctor.map₂

def mkLiftMap₂LiftExpr (e : Expr) : MetaM Expr := do
  let (``Quiver.Hom, #[_, _, f, _]) := (← whnfR <| ← inferType e).getAppFnArgs
    | throwError "{e} is not a morphism"
  let (``Quiver.Hom, #[_, _, a, _]) := (← whnfR <| ← inferType f).getAppFnArgs
    | throwError "{f} is not a morphism"
  let B ← inferType a
  mkAppM ``PrelaxFunctor.map₂ #[← mkAppM ``Pseudofunctor.toPrelaxFunctor
    #[← mkAppM ``FreeBicategory.lift #[← mkAppOptM ``Prefunctor.id #[B, none]]], ← free₂ e]

partial def genAssoc (src tar : Expr) : MetaM Expr := do
  match src.getAppFnArgs, tar.getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, _, _, f, g]), (``CategoryStruct.comp, #[_, _, _, _, _, f', h]) =>
    mkAppM ``Bicategory.whiskerLeft #[f, ← genAssoc g h]
  | _, _ => throwError "genAssoc failed"

open Lean Elab Tactic Meta

/-- Helper function for throwing exceptions. -/
def exception (g : MVarId) (msg : MessageData) : MetaM α :=
  throwTacticEx `bicategorical_coherence g msg

/-- Coherence tactic for bicategories. -/
def bicategory_coherence (g : MVarId) : MetaM Unit := g.withContext do
  -- TODO: is this `dsimp only` step necessary? It doesn't appear to be in the tests below.
  -- let (ty, _) ← dsimp (← g.getType) (← Simp.Context.ofNames [] true)
  let ty ← g.getType
  let some (_, lhs, rhs) := (← whnfR ty).eq? | exception g "Not an equation of morphisms."
  let lift_lhs ← mkLiftMap₂LiftExpr lhs
  let lift_rhs ← mkLiftMap₂LiftExpr rhs
  -- This new equation is defeq to the original by assumption
  -- on the `LiftHom` instances.
  let g₁ ← g.change (← mkEq lift_lhs lift_rhs)
  let [g₂] ← g₁.applyConst ``congrArg
    | exception g "congrArg failed in coherence"
  let [] ← g₂.applyConst ``Subsingleton.elim
    | exception g "This shouldn't happen; Subsingleton.elim does not create goals."

-- #check ReaderT.run (r := c)

elab "bicategory_coherence" : tactic => do bicategory_coherence (← getMainGoal)

end Mathlib.Tactic.Bicategory

section Bicategory

open CategoryTheory
open scoped Bicategory


variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

example {a : B} (f : a ⟶ a) : 𝟙 f ▷ f = 𝟙 (f ≫ f) := by whisker_simps

example (a b : ℤ) : a + b = b + a := by bicategory_coherence

example : (λ_ (𝟙 a)).hom = (ρ_ (𝟙 a)).hom := by bicategory_coherence
example : (λ_ (𝟙 a)).inv = (ρ_ (𝟙 a)).inv := by bicategory_coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (α_ f g h).inv ≫ (α_ f g h).hom = 𝟙 (f ≫ g ≫ h) :=
by bicategory_coherence
example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  Iso.inv (α_ f g h) ≫ Iso.hom (α_ f g h) = 𝟙 (f ≫ g ≫ h) :=
by bicategory_coherence

-- @[simp]
def comp' (f : a ⟶ b) (g : b ⟶ c) := f ≫ g

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
  f ◁ (α_ g h i).hom ≫ (α_ f g (h ≫ i)).inv ≫ (α_ (comp' f g) h i).inv =
    (α_ f (g ≫ h) i).inv ≫ (α_ f g h).inv ▷ i := by
  bicategory_coherence

example (f : a ⟶ b) (g : b ⟶ c) :
  f ◁ (λ_ g).inv ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g :=
by bicategory_coherence

example : 𝟙 (𝟙 a ≫ 𝟙 a) ≫ (λ_ (𝟙 a)).hom = 𝟙 (𝟙 a ≫ 𝟙 a) ≫ (ρ_ (𝟙 a)).hom := by
  bicategory_coherence

set_option profiler true in
example (f₁ : a ⟶ b) (f₂ : b ⟶ c) :
  (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).hom ≫
    𝟙 a ◁ (α_ (𝟙 a) f₁ f₂).inv ≫
      𝟙 a ◁ ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ f₂ ≫
        𝟙 a ◁ (α_ f₁ (𝟙 b) f₂).hom ≫
          (α_ (𝟙 a) f₁ (𝟙 b ≫ f₂)).inv ≫
            ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ (𝟙 b ≫ f₂) ≫
              (α_ f₁ (𝟙 b) (𝟙 b ≫ f₂)).hom ≫
                f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                  f₁ ◁ (α_ (𝟙 b) f₂ (𝟙 c)).inv ≫
                    f₁ ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ▷ 𝟙 c ≫
                      (f₁ ◁ (α_ f₂ (𝟙 c) (𝟙 c)).hom) ≫
                        (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).inv =
  ((λ_ (𝟙 a)).hom ▷ (f₁ ≫ f₂) ≫ (λ_ (f₁ ≫ f₂)).hom ≫ (ρ_ (f₁ ≫ f₂)).inv) ≫
    (f₁ ≫ f₂) ◁ (λ_ (𝟙 c)).inv :=
by bicategory_coherence

example (f g : a ⟶ a) (η : 𝟙 a ⟶ f) (θ : f ⟶ g) (w : false) :
  (λ_ (𝟙 a)).hom ≫ η ≫ θ = (ρ_ (𝟙 a)).hom ≫ η ≫ θ :=
by bicategory_coherence

end Bicategory
