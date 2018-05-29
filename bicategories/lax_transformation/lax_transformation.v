Require Import HoTT.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.

Section LaxTransformation.
  Context `{Univalence}.

  Local Open Scope bicategory_scope.

  (* For f ∈ Hom(Y₁,Y₂):
     - f_∗ : Hom(X,Y₁) → Hom(X,Y₂)
     - f^∗ : Hom(Y₂,X) → Hom(Y₁,X)
   *)
  Definition postcomp
             {C : BiCategory}
             {Y1 Y2 : C}
             (f : Hom C Y1 Y2)
             (X : C)
    : Functor (Hom C X Y1) (Hom C X Y2)
    := c_m o Functor.prod (const_functor f) 1.

  Definition precomp
             {C : BiCategory}
             {Y1 Y2 : C}
             (f : Hom C Y1 Y2)
             (X : C)
    : Functor (Hom C Y2 X) (Hom C Y1 X)
    := c_m o Functor.prod 1 (const_functor f).

  Record LaxTransformation {C D : BiCategory} (F G : LaxFunctor C D) :=
    {
      laxcomponent_of : forall X, Hom _ (F X) (G X);
      laxnaturality_of : forall {X Y : C},
          NaturalTransformation
            (precomp (laxcomponent_of X) (G Y) (* (σX)^* *)
            o @Fmor _ _ _ G X Y)%functor
            (postcomp (laxcomponent_of Y) (F X) (* (σY)_* *)
            o @Fmor _ _ _ F X Y);
      (* aka a natural family of two-cells
         (laxmorphism_of G f ⋅ laxcomponent_of X)
         ==> (laxcomponent_of Y ⋅ laxmorphism_of F f) *)
      naturality_id : forall {X : C},
        (laxnaturality_of (id_m X)
         o ((Fid G X) ∗ 1))%morphism
        = ((1 ∗ (Fid F X))
          o (inverse (un_r (F X) (G X)) (laxcomponent_of X))
          o (un_l _ _ (laxcomponent_of X)))%morphism;
      naturality_comp : forall {X Y Z : C} {f : Hom _ X Y} {g : Hom _ Y Z},
          (laxnaturality_of (g ⋅ f)
          o (Fcomp G (g,f) ∗ 1))%morphism
          = ((1 ∗ Fcomp F (g,f))
            o (assoc (laxcomponent_of Z, Fmor F g, Fmor F f))
            o (laxnaturality_of g ∗ 1)
            o ((inverse assoc)
                 (Fmor G g, laxcomponent_of Y, Fmor F f))
            o (1 ∗ laxnaturality_of f)
            o (assoc (Fmor G g, Fmor G f, laxcomponent_of X)))%morphism
    }.
End LaxTransformation.

Arguments laxcomponent_of {_ C D F G}.
Arguments laxnaturality_of {_ C D F G} _ {X Y}.