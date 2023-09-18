import Mathlib.CategoryTheory.Bicategory.Coherence
import Mathlib.Util.AtomM

set_option autoImplicit true

namespace Mathlib.Tactic.Bicategory

-- open Mathlib.Meta Qq NormNum Lean.Meta AtomM Lean.Elab
open Lean (MetaM Expr mkRawNatLit)
open Lean.Elab.Tactic
open CategoryTheory
-- open Lean

open Qq

-- set_option pp.collapseStructureProjections false

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

structure LiftHom₂ where
  /-- A 2-morphism in a bicategory -/
  hom₂ : Expr
  /-- A lifte of `hom₂` in the free bicategory -/
  lift : Expr
  /-- A proof of the fact that `lift` is a lift of `hom₂` -/
  pr : Expr

#print FreeBicategory.normalizeIso

def normalizeHomAux {B : Type u} [Quiver.{v + 1} B] {a : B} :
    ∀ {b c : B}, FreeBicategory.Hom a b → FreeBicategory.Hom b c → FreeBicategory.Hom a c
  | _, _, p, FreeBicategory.Hom.of f => p.comp (FreeBicategory.Hom.of f)
  | _, _, p, FreeBicategory.Hom.id _ => p
  | _, _, p, FreeBicategory.Hom.comp f g => normalizeHomAux (normalizeHomAux p f) g

def normalizeHom {B : Type u} [Quiver.{v + 1} B] {a b : B} (f : FreeBicategory.Hom a b) :
    FreeBicategory.Hom a b :=
  normalizeHomAux (FreeBicategory.Hom.id a) f

open FreeBicategory in
def normalizeHom₂Aux {B : Type u} [Quiver.{v + 1} B] {a : B} :
    ∀ {b c : B} (p : FreeBicategory.Hom a b) (f : FreeBicategory.Hom b c),
      Hom₂ (p.comp f) (normalizeHomAux p f)
  | _, _, _, Hom.of _ => Hom₂.id _
  | _, _, _, Hom.id b => Hom₂.right_unitor _
  | _, _, p, Hom.comp f g =>
    (Hom₂.associator_inv p f g).vcomp
      ((Hom₂.whisker_right g (normalizeHom₂Aux p f)).vcomp (normalizeHom₂Aux (normalizeHomAux p f) g))

open FreeBicategory in
def normalizeHom₂InvAux {B : Type u} [Quiver.{v + 1} B] {a : B} :
    ∀ {b c : B} (p : FreeBicategory.Hom a b) (f : FreeBicategory.Hom b c),
      Hom₂ (normalizeHomAux p f) (p.comp f)
  | _, _, _, Hom.of _ => Hom₂.id _
  | _, _, _, Hom.id b => Hom₂.right_unitor_inv _
  | _, _, p, Hom.comp f g =>
    (normalizeHom₂InvAux (normalizeHomAux p f) g).vcomp
      ((Hom₂.whisker_right g (normalizeHom₂InvAux p f)).vcomp (Hom₂.associator p f g))

def normalizeHom₂ {B : Type u} [Quiver.{v + 1} B] {a b : B} (f : FreeBicategory.Hom a b) :
    FreeBicategory.Hom₂ f (normalizeHom f) :=
  (FreeBicategory.Hom₂.left_unitor_inv _).vcomp (normalizeHom₂Aux (FreeBicategory.Hom.id a) f)

def normalizeHom₂Inv {B : Type u} [Quiver.{v + 1} B] {a b : B} (f : FreeBicategory.Hom a b) :
    FreeBicategory.Hom₂ (normalizeHom f) f :=
  (normalizeHom₂InvAux (FreeBicategory.Hom.id a) f).vcomp (FreeBicategory.Hom₂.left_unitor _)

partial def normalize (p f : Expr) : MetaM (Expr × Expr) := do
  match f.getAppFnArgs with
  | (``CategoryStruct.id, _) =>
    let η ← mkAppM ``Bicategory.rightUnitor #[p]
    return (p, η)
  -- `(α_ _ _ _).symm ≪≫ whiskerRightIso (normalizeIso p f) g ≪≫ normalizeIso (normalizeAux p f) g`
  | (``CategoryStruct.comp, #[_, _, _, _, _, f, g]) =>
    let η₀ ← normalize p f
    let η₀' ← normalize η₀.1 g
    let η₂ := η₀'.2
    let α ← mkAppM ``Iso.symm #[← mkAppM ``Bicategory.associator #[p, f, g]]
    let f' := η₀'.1
    match (η₀.2).getAppFnArgs with
    | (``Iso.refl, _) =>
      let η ← mkAppM ``Iso.trans #[α, η₂]
      return (f', η)
    | _ =>
      let η₁ ← mkAppM ``Bicategory.whiskerRightIso #[η₀.2, g]
      match η₂.getAppFnArgs with
      | (``Iso.refl, _) =>
        let η ← mkAppM ``Iso.trans #[α, η₁]
        return (f', η)
      | _ =>
        let η ← mkAppM ``Iso.trans #[η₁, η₂]
        let η ← mkAppM ``Iso.trans #[α, η]
        return (f', η)
  | _ =>
    let f' ← mkAppM ``CategoryStruct.comp #[p, f]
    let η ← mkAppM ``Iso.refl #[f']
    return (f', η)

def Bicategory.toQuiver {B : Type} [Bicategory B] : Quiver B := inferInstance

#eval show TermElabM _ from do
  withLocalDecl `B .default (.sort (.succ (.zero))) <| fun B => do
  withLocalDecl `_h .instImplicit (mkAppN (.const ``Bicategory [ .zero,  .zero,  .zero]) #[B]) <| fun _h => do
  withLocalDecl `a .default B <| fun a => do
  withLocalDecl `b .default B <| fun b => do
  withLocalDecl `c .default B <| fun c => do
  withLocalDecl `d .default B <| fun d => do
  withLocalDecl `f .default (← mkAppOptM ``Quiver.Hom #[B, ← mkAppOptM ``Bicategory.toQuiver #[B, _h], a, b]) <| fun f => do
  withLocalDecl `g .default (← mkAppOptM ``Quiver.Hom #[B, ← mkAppOptM ``Bicategory.toQuiver #[B, _h], b, c]) <| fun g => do
  withLocalDecl `h .default (← mkAppOptM ``Quiver.Hom #[B, ← mkAppOptM ``Bicategory.toQuiver #[B, _h], c, d]) <| fun h => do
    let f ← Term.exprToSyntax f
    let g ← Term.exprToSyntax g
    let h ← Term.exprToSyntax h
    let fg ← Elab.Term.elabTermAndSynthesize (← `($f ≫ (𝟙 _ ≫ $g) ≫ 𝟙 _ ≫ $h)) none
    IO.println (← ppExpr fg)
    IO.println (← ppExpr (← normalize (← mkAppM ``CategoryStruct.id #[a]) fg).1)
    let (e, _) ← dsimp (← mkAppM ``Iso.hom #[(← normalize (← mkAppM ``CategoryStruct.id #[a]) fg).2]) (← Simp.Context.ofNames)
    IO.println (← ppExpr e)

#eval show TermElabM _ from do
  withLocalDecl `B .default (.sort (.succ (.zero))) <| fun B => do
  withLocalDecl `_h .instImplicit (mkAppN (.const ``Bicategory [ .zero,  .zero,  .zero]) #[B]) <| fun _h => do
  withLocalDecl `a .default B <| fun a => do
  withLocalDecl `b .default B <| fun b => do
  withLocalDecl `f .default (← mkAppOptM ``Quiver.Hom #[B, ← mkAppOptM ``Bicategory.toQuiver #[B, _h], a, b]) <| fun f => do
    -- IO.println (← ppExpr (← Elab.Term.elabTermAndSynthesize (← `($(← Term.exprToSyntax f) ≫ $(← Term.exprToSyntax g))) none))
    let f ← Term.exprToSyntax f
    let fg ← Elab.Term.elabTermAndSynthesize (← `(𝟙 _ ≫ $f)) none
    IO.println (← ppExpr (← normalize (← mkAppM ``CategoryStruct.id #[a]) fg).1)
    IO.println (← ppExpr (← normalize (← mkAppM ``CategoryStruct.id #[a]) fg).2)
    let (e, _) ← dsimp (← mkAppM ``Iso.hom #[(← normalize (← mkAppM ``CategoryStruct.id #[a]) fg).2]) (← Simp.Context.ofNames)
    IO.println (← ppExpr e)

partial def free₁ (e : Expr) : MetaM Expr := do
  -- let (e, _) ← dsimp e (← Simp.Context.ofNames)
  let (``Quiver.Hom, #[_, _, a, b]) := (← whnfR <| ← inferType e).getAppFnArgs
    | throwError "{e} is not a morphism"
  let c ← mkFreshExprMVar (← inferType a)
  let f ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[a, c])
  let g ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[c, b])
  if ← isDefEq e (← mkAppM ``CategoryStruct.comp #[f, g]) then
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

-- local instance homCategory' (a b : B) : Category (FreeBicategory.Hom a b) :=
--   FreeBicategory.homCategory a b

open Term

elab "lift_to_free " t:term : term => do
  -- withMainContext do
  let f ← Term.elabTerm t none
  free₁ f

-- syntax (name := lift_to_free) "lift" term : term

-- @[term_elab lift_to_free]
-- def liftToFreeImpl : TermElab := fun stx expectedType? => do
--   free₁ `($stx)

def hoge {B : Type u} [Bicategory.{w, v} B] {a b : B} (f : a ⟶ b) : FreeBicategory.Hom a b :=
  lift_to_free (f ≫ 𝟙 b)

#print hoge

def genAssoc {B : Type u} [Bicategory.{w, v} B] {a b : B}
    (f g : a ⟶ b)
    (f' : FreeBicategory.Hom a b)
    (g' : FreeBicategory.Hom a b)
    (fg' : normalizeHom f' = normalizeHom g' := by rfl)
    (prf : (FreeBicategory.lift (𝟭q B)).map f' = f := by rfl)
    (prg : (FreeBicategory.lift (𝟭q B)).map g' = g := by rfl) : f ⟶ g :=
  let ι : FreeBicategory.Hom₂ f' g' :=
    (normalizeHom₂ f').vcomp (FreeBicategory.Hom₂.vcomp (fg' ▸ FreeBicategory.Hom₂.id _) (normalizeHom₂Inv g'))
  eqToHom prf.symm ≫ ((FreeBicategory.lift (𝟭q B)).map₂ <| Quot.mk _ ι) ≫ eqToHom prg

def bicategoricalComp {B : Type u} [Bicategory.{w, v} B] {a b : B}
    {f g h i : a ⟶ b}
    (g' : FreeBicategory.Hom a b := lift_to_free g)
    (h' : FreeBicategory.Hom a b := lift_to_free h)
    (gh' : normalizeHom g' = normalizeHom h' := by rfl)
    (prg : (FreeBicategory.lift (𝟭q B)).map g' = g := by rfl)
    (prh : (FreeBicategory.lift (𝟭q B)).map h' = h := by rfl)
    (η : f ⟶ g) (θ : h ⟶ i) : f ⟶ i :=
  η ≫ genAssoc g h g' h' gh' prg prh ≫ θ

infixr:80 " ⊗≫ " => Mathlib.Tactic.Bicategory.bicategoricalComp

example {B : Type u} [Bicategory.{w, v} B] {a b : B}
    {f : a ⟶ b} : f ≫ 𝟙 b ⟶ f :=
  genAssoc (f ≫ 𝟙 b) f (lift_to_free (f ≫ 𝟙 b)) (lift_to_free f)

structure bicatNormalize.Result where
  src : Expr
  tar : Expr
  hom : Array Expr
  prf : Expr

partial def bicatNormalize (n : Expr) (η : Expr) : MetaM bicatNormalize.Result := do
  match η.getAppFnArgs with
  | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
    let ⟨s, t, ηs, prf⟩ ← bicatNormalize n η
    return ⟨s, t, ηs, prf⟩
  | _ => throwError "Normalization failed : {η}"

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

-- variable {B : Type u} [Bicategory.{w, v} B] {a b c d e : B}

-- theorem lift_map₂_comp {a b : FreeBicategory B} {f g : a ⟶ b} (η : f ⟶ g) :
--     (FreeBicategory.lift (Prefunctor.id : Prefunctor B B)).map₂ η =

-- partial def free₂ (e : Expr) : MetaM LiftHom₂ := do
--   let error : MetaM Expr := throwError "{← whnfR e} is not a structural 2-morphism"
--   -- IO.println (← ppExpr <| (← whnfR e))
--   match e.getAppFnArgs with
--   | (``CategoryStruct.comp, #[_, _, _, _, _, η, θ]) =>
--     ⟨e, mkAppM ``CategoryStruct.comp #[← free₂ η, ← free₂ θ], _⟩
--   | (``Bicategory.whiskerLeft, #[_, _, _, _, _, f, _, _, η]) =>
--     mkAppM ``Bicategory.whiskerLeft #[← free₁ f, ← free₂ η]
--   | (``Bicategory.whiskerRight, #[_, _, _, _, _, _, _, η, h]) =>
--     mkAppM ``Bicategory.whiskerRight #[← free₂ η, ← free₁ h]
--   | (``CategoryStruct.id, #[_, _, f]) =>
--     mkAppM ``CategoryStruct.id #[← free₁ f]
--   | (``Iso.hom, #[_, _, _, _, η]) =>
--     match (← whnfR η).getAppFnArgs with
--     | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
--       mkAppM ``Iso.hom #[← mkAppM ``Bicategory.associator #[← free₁ f, ← free₁ g, ← free₁ h]]
--     | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
--       mkAppM ``Iso.hom #[← mkAppM ``Bicategory.leftUnitor #[← free₁ f]]
--     | (``Bicategory.rightUnitor, #[_, _, _, _, f]) =>
--       mkAppM ``Iso.hom #[← mkAppM ``Bicategory.rightUnitor #[← free₁ f]]
--     | _ => throwError "{← whnf η} is not a structural 2-morphism"
--   | (``Iso.inv, #[_, _, _, _, η]) =>
--     match (← whnfR η).getAppFnArgs with
--     | (``Bicategory.associator, #[_, _, _, _, _, _, f, g, h]) =>
--       mkAppM ``Iso.inv #[← mkAppM ``Bicategory.associator #[← free₁ f, ← free₁ g, ← free₁ h]]
--     | (``Bicategory.leftUnitor, #[_, _, _, _, f]) =>
--       mkAppM ``Iso.inv #[← mkAppM ``Bicategory.leftUnitor #[← free₁ f]]
--     | (``Bicategory.rightUnitor, #[_, _, _, _, f]) =>
--       mkAppM ``Iso.inv #[← mkAppM ``Bicategory.rightUnitor #[← free₁ f]]
--     | _ => error
--   | _ => error

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

def objType (η : Expr) : MetaM Expr := do
  let (``Quiver.Hom, #[_, _, f, _]) := (← inferType η).getAppFnArgs
    | throwError "{η} is not a morphism"
  let (``Quiver.Hom, #[_, _, a, _]) := (← inferType f).getAppFnArgs
    | throwError "{f} is not a morphism"
  inferType a

def mkLiftMap₂LiftExpr (e : Expr) : MetaM Expr := do
  -- let (``Quiver.Hom, #[_, _, f, _]) := (← whnfR <| ← inferType e).getAppFnArgs
  --   | throwError "{e} is not a morphism"
  -- let (``Quiver.Hom, #[_, _, a, _]) := (← whnfR <| ← inferType f).getAppFnArgs
  --   | throwError "{f} is not a morphism"
  let B ← objType e
  mkAppM ``PrelaxFunctor.map₂ #[← mkAppM ``Pseudofunctor.toPrelaxFunctor
    #[← mkAppM ``FreeBicategory.lift #[← mkAppOptM ``Prefunctor.id #[B, none]]], ← free₂ e]

-- partial def genAssoc (src tar : Expr) : MetaM Expr := do
--   match src.getAppFnArgs, tar.getAppFnArgs with
--   | (``CategoryStruct.comp, #[_, _, _, _, _, f, g]), (``CategoryStruct.comp, #[_, _, _, _, _, f', h]) =>
--     mkAppM ``Bicategory.whiskerLeft #[f, ← genAssoc g h]
--   | _, _ => throwError "genAssoc failed"

-- instance genAssoc.whiskerLeft (f : a ⟶ b) (g h : b ⟶ c) [LiftHom f] [LiftHom g] [LiftHom h]
--     [BicategoricalCoherence g h] : BicategoricalCoherence (f ≫ g) (f ≫ h) :=
--   ⟨f ◁ BicategoricalCoherence.hom g h⟩

-- inductive genAssoc : Type where
--   | id (f : Expr) : genAssoc
--   | assoc (f g h : Expr) : genAssoc
--   | assocInv (f g h : Expr) : genAssoc
--   | leftUnitor (f : Expr) : genAssoc
--   | leftUnitorInv (f : Expr) : genAssoc
--   | rightUnitor (f : Expr) : genAssoc
--   | rightUnitorInv (f : Expr) : genAssoc
--   | whiskerLeft (f : Expr) (η : genAssoc) : genAssoc
--   | whiskerRight (f : Expr) (η : genAssoc) : genAssoc

partial def genAssoc (src tar : Expr) : MetaM Expr := do
  let (``Quiver.Hom, #[_, _, _a, _]) := (← whnfR <| ← inferType src).getAppFnArgs
    | throwError "{src} is not a morphism"
  let B ← inferType _a
  let a ← mkFreshExprMVar B
  let b ← mkFreshExprMVar B
  let c ← mkFreshExprMVar B
  let f ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[a, b])
  let g ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[b, c])
  let h ← mkFreshExprMVar (← mkAppM ``Quiver.Hom #[b, c])

  if ← isDefEq src (← mkAppM ``CategoryStruct.comp #[f, g]) then
    if ← isDefEq tar (← mkAppM ``CategoryStruct.comp #[f, h]) then
      mkAppM ``Bicategory.whiskerLeft #[f, ← genAssoc g h]
    else throwError "genAssoc failed"
  else


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
  IO.println (← ppExpr (← g₁.getType))
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

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
  (CategoryTheory.Bicategory.associator (𝟙 a) f ((𝟙 b ≫ g) ≫ 𝟙 c ≫ h)).inv ≫
  CategoryTheory.Bicategory.whiskerRight (𝟙 (𝟙 a ≫ f)) ((𝟙 b ≫ g) ≫ 𝟙 c ≫ h) ≫
    (CategoryTheory.Bicategory.associator (𝟙 a ≫ f) (𝟙 b ≫ g) (𝟙 c ≫ h)).inv ≫
      CategoryTheory.Bicategory.whiskerRight
          ((CategoryTheory.Bicategory.associator (𝟙 a ≫ f) (𝟙 b) g).inv ≫
            CategoryTheory.Bicategory.whiskerRight (CategoryTheory.Bicategory.rightUnitor (𝟙 a ≫ f)).hom g ≫
              𝟙 ((𝟙 a ≫ f) ≫ g))
          (𝟙 c ≫ h) ≫
        (CategoryTheory.Bicategory.associator ((𝟙 a ≫ f) ≫ g) (𝟙 c) h).inv ≫
          CategoryTheory.Bicategory.whiskerRight (CategoryTheory.Bicategory.rightUnitor ((𝟙 a ≫ f) ≫ g)).hom h ≫
            𝟙 (((𝟙 a ≫ f) ≫ g) ≫ h) =
  (CategoryTheory.Bicategory.associator (𝟙 a) f ((𝟙 b ≫ g) ≫ 𝟙 c ≫ h)).inv ≫
  (CategoryTheory.Bicategory.associator (𝟙 a ≫ f) (𝟙 b ≫ g) (𝟙 c ≫ h)).inv ≫
    CategoryTheory.Bicategory.whiskerRight
        ((CategoryTheory.Bicategory.associator (𝟙 a ≫ f) (𝟙 b) g).inv ≫
          CategoryTheory.Bicategory.whiskerRight (CategoryTheory.Bicategory.rightUnitor (𝟙 a ≫ f)).hom g)
        (𝟙 c ≫ h) ≫
      (CategoryTheory.Bicategory.associator ((𝟙 a ≫ f) ≫ g) (𝟙 c) h).inv ≫
        CategoryTheory.Bicategory.whiskerRight (CategoryTheory.Bicategory.rightUnitor ((𝟙 a ≫ f) ≫ g)).hom h := by
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
