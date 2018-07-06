Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     bicategory.bicategory lax_functor.lax_functor general_category.

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

  Record LaxTransformation_d {C D : BiCategory} (F G : LaxFunctor C D) :=
    Build_LaxTransformation_d
      {
        laxcomponent_of_d : forall X, Hom _ (F X) (G X) ;
        laxnaturality_of_d : forall {X Y : C},
            NaturalTransformation
              (precomp (laxcomponent_of_d X) (G Y) (* (σX)^* *)
                       o @Fmor _ _ _ G X Y)%functor
              (postcomp (laxcomponent_of_d Y) (F X) (* (σY)_* *)
                        o @Fmor _ _ _ F X Y)
        (* aka a natural family of two-cells
         (laxmorphism_of G f ⋅ laxcomponent_of X)
         ==> (laxcomponent_of Y ⋅ laxmorphism_of F f) *)
      }.

  Arguments Build_LaxTransformation_d {C D F G} _ _.
  Arguments laxcomponent_of_d {C D F G} η X : rename.
  Arguments laxnaturality_of_d {C D F G} η {X Y} : rename.
  
  Definition is_lax_transformation
             {C D : BiCategory}
             {F G : LaxFunctor C D}
             (η : LaxTransformation_d F G)
    : Type
    := (forall {X : C},
           (laxnaturality_of_d η (id_m X)
                               o ((Fid G X) ∗ 1))%morphism
           = ((1 ∗ (Fid F X))
                o (inverse (un_r (F X) (G X)) (laxcomponent_of_d η X))
                o (un_l _ _ (laxcomponent_of_d η X)))%morphism)
       *
       (forall {X Y Z : C} {f : Hom _ X Y} {g : Hom _ Y Z},
           (laxnaturality_of_d η (g · f)
                               o (Fcomp G (g,f) ∗ 1))%morphism
           = ((1 ∗ Fcomp F (g,f))
                o (assoc (laxcomponent_of_d η Z, Fmor F g, Fmor F f))
                o (laxnaturality_of_d η g ∗ 1)
                o ((inverse assoc)
                     (Fmor G g, laxcomponent_of_d η Y, Fmor F f))
                o (1 ∗ laxnaturality_of_d η f)
                o (assoc (Fmor G g, Fmor G f, laxcomponent_of_d η X))))%morphism.

  Global Instance is_lax_hprop
         {C D : BiCategory}
         {F G : LaxFunctor C D}
         (η : LaxTransformation_d F G)
    : IsHProp (is_lax_transformation η)
    := _.

  Definition LaxTransformation {C D : BiCategory} (F G : LaxFunctor C D)
    := {η : LaxTransformation_d F G & is_lax_transformation η}.

  Definition Build_LaxTransformation
             {C D : BiCategory}
             {F G : LaxFunctor C D}
             (η : LaxTransformation_d F G)
             (Hη : is_lax_transformation η)
    : LaxTransformation F G
    := (η;Hη).

  Definition laxcomponent_of
             {C D : BiCategory}
             {F G : LaxFunctor C D}
             (η : LaxTransformation F G)
    : forall X, Hom _ (F X) (G X)
    := laxcomponent_of_d η.1.

  Definition laxnaturality_of
             {C D : BiCategory}
             {F G : LaxFunctor C D}
             (η : LaxTransformation F G)
             {X Y : C}
    : NaturalTransformation
        (precomp (laxcomponent_of η X) (G Y) (* (σX)^* *)
                 o @Fmor _ _ _ G X Y)%functor
        (postcomp (laxcomponent_of η Y) (F X) (* (σY)_* *)
                  o @Fmor _ _ _ F X Y)
    := @laxnaturality_of_d _ _ _ _ η.1 X Y.

  Definition naturality_id
             {C D : BiCategory}
             {F G : LaxFunctor C D}
             (η : LaxTransformation F G)
    : forall {X : C},
      (laxnaturality_of η (id_m X)
                        o ((Fid G X) ∗ 1))%morphism
      = ((1 ∗ (Fid F X))
           o (inverse (un_r (F X) (G X)) (laxcomponent_of η X))
           o (un_l _ _ (laxcomponent_of η X)))%morphism
    := Datatypes.fst η.2.

  Definition naturality_comp
             {C D : BiCategory}
             {F G : LaxFunctor C D}
             (η : LaxTransformation F G)
    : forall {X Y Z : C} {f : Hom _ X Y} {g : Hom _ Y Z},
      (laxnaturality_of η (g · f)
                        o (Fcomp G (g,f) ∗ 1))%morphism
      = ((1 ∗ Fcomp F (g,f))
           o (assoc (laxcomponent_of η Z, Fmor F g, Fmor F f))
           o (laxnaturality_of η g ∗ 1)
           o ((inverse assoc)
                (Fmor G g, laxcomponent_of η Y, Fmor F f))
           o (1 ∗ laxnaturality_of η f)
           o (assoc (Fmor G g, Fmor G f, laxcomponent_of η X)))%morphism
    := Datatypes.snd η.2.
End LaxTransformation.

Arguments Build_LaxTransformation_d {_ C D F G} _ _.
Arguments laxcomponent_of_d {_ C D F G} η X : rename.
Arguments laxnaturality_of_d {_ C D F G} η {X Y} : rename.

Class is_pseudo_transformation
      `{Univalence}
      {C D : BiCategory}
      {F G : LaxFunctor C D}
      (η : LaxTransformation F G)
  := { laxnaturality_of_iso : forall {X Y : C},
         @IsIsomorphism (_ -> _)
                        _
                        _
                        (@laxnaturality_of _ _ _ _ _ η X Y)
     }.

Global Instance laxnaturality_of_iso_class
       `{Univalence}
       {C D : BiCategory}
       {F G : LaxFunctor C D}
       (η : LaxTransformation F G)
       `{@is_pseudo_transformation _ _ _ _ _ η}
       (X Y : C)
  : @IsIsomorphism (_ -> _) _ _ (@laxnaturality_of _ _ _ _ _ η X Y).
Proof.
  apply laxnaturality_of_iso.
Defined.

Local Open Scope bicategory.

Section RawBuilder.
  Context `{Univalence}
          {C D : BiCategory}.  
  
  Record PseudoTransformation_d
         (F G : LaxFunctor C D)
    := Build_PseudoTransformation_d
         { laxcomponent_of_rd : forall (X : C), Hom D (F X) (G X) ;
           laxnaturality_of_rd : forall (X Y : C) (f : Hom C X Y),
               Core.morphism (Hom D (F X) (G Y))
                             (Fmor G f · laxcomponent_of_rd X)
                             (laxcomponent_of_rd Y · Fmor F f) ;
           laxnaturality_of_rd_inv : forall (X Y : C) (f : Hom C X Y),
               Core.morphism (Hom D (F X) (G Y))
                             (laxcomponent_of_rd Y · Fmor F f)
                             (Fmor G f · laxcomponent_of_rd X)
         }.

  Arguments laxcomponent_of_rd {F G} _ X.
  Arguments laxnaturality_of_rd {F G} _ X Y f.
  Arguments laxnaturality_of_rd_inv {F G} _ X Y f.

  Definition is_pseudo_transformation_rd
             {F G : LaxFunctor C D}
             (η : PseudoTransformation_d F G)
    : Type.
  Proof.
    refine (_ * _ * _ * _ * _ * _).
    - exact (forall (X Y : C)
                    (f g : Hom C X Y)
                    (α : morphism (Hom C X Y) f g),
                (laxnaturality_of_rd η X Y g o hcomp 1 (Fmor G _1 α)) =
                (hcomp (Fmor F _1 α) 1 o laxnaturality_of_rd η X Y f))%morphism.
    - exact (forall (X : C),
                (laxnaturality_of_rd η X X (id_m X) o (Fid G X ∗ 1))
                =
                ((1 ∗ Fid F X)
                   o (inverse (un_r (F X) (G X))) (laxcomponent_of_rd η X)
                   o (un_l (F X) (G X)) (laxcomponent_of_rd η X)))%morphism.
    - exact (forall (X Y Z : C) (f : Hom C X Y) (g : Hom C Y Z),
                ((laxnaturality_of_rd η X Z (g · f))
                   o ((Fcomp G) (g, f) ∗ 1))
                =
                ((1 ∗ (Fcomp F) (g, f))
                   o assoc (laxcomponent_of_rd η Z, (Fmor F) g, (Fmor F) f)
                   o (laxnaturality_of_rd η Y Z g ∗ 1)
                   o (inverse assoc) ((Fmor G) g, laxcomponent_of_rd η Y, (Fmor F) f)
                   o (1 ∗ laxnaturality_of_rd η X Y f)
                   o assoc ((Fmor G) g, (Fmor G) f, laxcomponent_of_rd η X)))%morphism.
    - exact (forall (X Y : C)
                    (f g : Hom C X Y)
                    (α : morphism (Hom C X Y) f g),
                (laxnaturality_of_rd_inv η X Y g o hcomp (Fmor F _1 α) 1) =
                (hcomp 1 (Fmor G _1 α) o laxnaturality_of_rd_inv η X Y f))%morphism.
    - exact (forall (X Y : C)
                    (f : Hom C X Y),
                (laxnaturality_of_rd_inv η X Y f)
                  o laxnaturality_of_rd η X Y f
                = 1)%morphism.
    - exact (forall (X Y : C)
                    (f : Hom C X Y),
                (laxnaturality_of_rd η X Y f)
                  o laxnaturality_of_rd_inv η X Y f
                = 1)%morphism.
  Defined.

  Definition Build_PseudoTransformation
             {F G : LaxFunctor C D}
             (η : PseudoTransformation_d F G)
             (Hη : is_pseudo_transformation_rd η)
    : LaxTransformation F G.
  Proof.
    simple refine (Build_LaxTransformation _ _).
    - simple refine (Build_LaxTransformation_d _ _).
      + exact (laxcomponent_of_rd η).
      + intros X Y.
        simple refine (Build_NaturalTransformation _ _ _ _).
        * exact (laxnaturality_of_rd η X Y).
        * apply Hη.
    - destruct Hη as [[[[[H₁ H₂] H₃] H₄] H₅] H₆].
      exact (H₂,H₃).
  Defined.

  Global Instance Build_Pseudo_is_pseudo
         {F G : LaxFunctor C D}
         (η : PseudoTransformation_d F G)
         (Hη : is_pseudo_transformation_rd η)
    : is_pseudo_transformation (Build_PseudoTransformation η Hη).
  Proof.
    destruct Hη as [[[[[H₁ H₂] H₃] H₄] H₅] H₆].
    split.
    intros X Y.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - simple refine (Build_NaturalTransformation _ _ _ _).
      + exact (laxnaturality_of_rd_inv η X Y).
      + exact (H₄ X Y).
    - apply path_natural_transformation.
      exact (H₅ X Y).
    - apply path_natural_transformation.
      exact (H₆ X Y).
  Defined.
End RawBuilder.

Arguments Build_PseudoTransformation_d {_ C D F G}.
Arguments Build_PseudoTransformation {_ C D F G}.