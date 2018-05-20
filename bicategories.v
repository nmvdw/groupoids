Require Import HoTT.
From HoTT.Categories Require Import
  Category Functor NaturalTransformation FunctorCategory.

Definition prod_assoc (C D E : PreCategory)
  : Functor (C * (D * E)) ((C * D) * E).
Proof.
  simple refine (Build_Functor (C * (D * E))
                               ((C * D) * E)
                               (fun X => ((fst X, fst(snd X)), snd(snd X)))
                               _ _ _).
  - refine (fun X Y f => ((_,_), _)) ; apply f.
  - reflexivity.
  - reflexivity.
Defined.

Definition assoc_prod (C D E : PreCategory)
  : Functor ((C * D) * E) (C * (D * E)).
Proof.
  simple refine (Build_Functor ((C * D) * E)
                               (C * (D * E))
                               _
                               _ _ _).
  - intros [[a b] c].
    exact (a,(b,c)).
  - refine (fun X Y f => (_,(_, _))) ; apply f.
  - reflexivity.
  - reflexivity.
Defined.

Definition const_functor
           {C D : PreCategory}
           (X : D)
  : Functor C D
  := Build_Functor C
                   D
                   (fun _ => X)
                   (fun _ _ _ => Category.identity X)
                   (fun _ _ _ _ _ => (left_identity _ _ _ _)^)
                   (fun _ => idpath).

Definition pair
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F₁ F₂ : Functor C₁ C₂}
           {G₁ G₂ : Functor D₁ D₂}
           (af : NaturalTransformation F₁ F₂)
           (ag : NaturalTransformation G₁ G₂)
  : NaturalTransformation (F₁,G₁) (F₂,G₂).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - exact (fun X => (af (fst X),ag (snd X))).
  - exact (fun X Y f => path_prod' (commutes af _ _ _) (commutes ag _ _ _)).
Defined.

Definition pair_l
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F₁ F₂ : Functor C₁ C₂}
           {G : Functor D₁ D₂}
           (af : NaturalTransformation F₁ F₂)
  : NaturalTransformation (F₁,G) (F₂,G)
  := pair af 1.

Definition pair_r
           {C₁ D₁ C₂ D₂ : PreCategory}
           {F : Functor C₁ C₂}
           {G₁ G₂ : Functor D₁ D₂}
           (ag : NaturalTransformation G₁ G₂)
  : NaturalTransformation (F,G₁) (F,G₂)
  := pair 1 ag.

Record BiCategory `{Univalence} :=
  Build_BiCategory {
      Obj :> Type ;
      Hom : Obj -> Obj -> PreCategory ;
      id_m : forall (x : Obj), Hom x x ;
      c_m : forall {x y z : Obj}, Functor (Category.prod (Hom y z) (Hom x y)) (Hom x z) ;
      un_l : forall (X Y : Obj),
          NaturalTransformation (@c_m X Y Y o (const_functor (id_m Y) * 1))
                                1 ;
      un_l_iso :> forall (X Y : Obj),
         @IsIsomorphism (Hom X Y -> Hom X Y) _ _ (un_l X Y) ;
      un_r : forall (X Y : Obj),
          NaturalTransformation (@c_m X X Y o (1 * const_functor (id_m X)))
                                1 ;
      un_r_iso :> forall (X Y : Obj),
          @IsIsomorphism (Hom X Y -> Hom X Y) _ _ (un_r X Y) ;
      assoc : forall (w x y z : Obj),
        NaturalTransformation
          ((c_m o (c_m, 1)))
          (c_m o (1, c_m) o (assoc_prod (Hom y z) (Hom x y) (Hom w x))) ;
      assoc_iso :> forall (w x y z : Obj), @IsIsomorphism
                                            ((Hom y z * Hom x y) * Hom w x -> Hom w z)
                                            _
                                            _
                                            (assoc w x y z) ;
      triangle : (forall (x y z : Obj) (g : Hom y z) (f : Hom x y),
                     @morphism_of _
                                  _
                                  c_m
                                  (c_m (g,id_m y),f)
                                  (g,f)
                                  ((un_r y z) g, 1)
                     =
                     (@morphism_of _
                                   _
                                   c_m
                                   (g,c_m (id_m y,f))
                                   (g,f)
                                   (1,un_l x y f))
                       o
                       (assoc x y y z) (g, id_m y, f))%morphism ;
      pentagon : (forall (v w x y z : Obj)
                         (k : Hom y z) (h : Hom x y) (g : Hom w x) (f : Hom v w),
                     (assoc v x y z (k,h,c_m (g,f)))
                       o assoc v w x z (c_m (k, h), g, f)
                     = (@morphism_of _
                                     _
                                     (@c_m v y z)
                                     (k,c_m (c_m (h,g),f))
                                     (k,c_m (h,c_m (g,f)))
                                     (1,assoc v w x y (h,g,f)))
                         o (assoc v w y z (k,c_m (h,g),f))
                         o
                         (@morphism_of _
                                       _
                                       (@c_m v w z)
                                       (c_m (c_m (k,h),g),f)
                                       (c_m (k,c_m (h,g)),f)
                                       (assoc w x y z (k,h,g),1)))%morphism
    }.

Arguments id_m {_} {B} x : rename.
Arguments c_m {_} {B} {x y z} : rename.
Arguments un_l {_ B} X Y : rename.
Arguments un_r {_ B} X Y : rename.
Arguments assoc {_ B} w x y z : rename.

Delimit Scope bicategory_scope with bicategory.
Bind Scope bicategory_scope with BiCategory.
Notation "f '⋅' g" := (c_m (f,g)) (at level 80): bicategory_scope.

Section BiCategory.
  Context `{Univalence}.

  Definition one_cell {BC : BiCategory} := Hom BC.
  Definition two_cell {BC : BiCategory} {A B : BC}
             (f g : one_cell A B) := morphism _ f g.
  Definition hcomp
             {BC : BiCategory} {A B C : BC}
             {f f' : one_cell A B} {g g' : one_cell B C}
             (α : two_cell f f') (β : two_cell g g')
    : (two_cell (g ⋅ f) (g' ⋅ f'))%bicategory
    := (c_m _1 ((β, α) : morphism (Hom _ B C * Hom _ A B) (g,f) (g',f')))%morphism.

  Local Notation "f '∗' g" := (hcomp g f) (at level 80) : bicategory_scope.

  Local Open Scope bicategory_scope.

  Definition interchange
             (C : BiCategory)
             {X Y Z : C}
             {p q r : one_cell X Y}
             {p' q' r' : one_cell Y Z}
             (h : two_cell p q) (h' : two_cell p' q')
             (k : two_cell q r) (k' : two_cell q' r')
    : (((k' o h') ∗ (k o h)) = ((k' ∗ k) o (h' ∗ h)))%morphism.
  Proof.
    rewrite <- composition_of.
    cbn.
    reflexivity.
  Defined.

End BiCategory.

Notation "f '∗' g" := (hcomp g f) (at level 80) : bicategory_scope.


Section TwoTypeBiGroupoid.
  Context `{Univalence}.

  Definition oneto (X : Type) `{IsTrunc 1 X} : PreCategory
    := Core.groupoid_category X.

  Definition oneto_cat (X : Type) `{IsTrunc 2 X} (x y : X) : IsCategory (oneto (x = y)).
  Proof.
    intros p q ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α. simpl.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros r ; induction r.
      reflexivity.
  Defined.

  Definition concat_functor
             {X : Type} `{IsTrunc 2 X}
             (x y z : X)
    : Functor (oneto (y = z) * oneto (x = y)) (oneto (x = z)).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun p => snd p @ fst p).
    - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
      induction r₁, r₂ ; reflexivity.
    - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] [s₁ s₂] [t₁ t₂] ; cbn in *.
      induction s₁, t₁, s₂, t₂ ; reflexivity.
    - intros [p₁ p₂] ; reflexivity.
  Defined.

  Definition pUnitor_l
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : NaturalTransformation
        (concat_functor x y y o (@const_functor _ (oneto (y = y)) idpath * 1))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact concat_p1.
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition pUnitor_l_inv
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : NaturalTransformation
        1
        (concat_functor x y y o (@const_functor _ (oneto (y = y)) idpath * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => (concat_p1 p)^).
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance pUnitor_l_iso {X : Type} `{IsTrunc 2 X} (x y : X)
    : @IsIsomorphism (oneto (x = y) -> oneto (x = y)) _ _ (pUnitor_l x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
  Defined.

  Definition pUnitor_r
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : NaturalTransformation
        (concat_functor x x y o (1 * @const_functor _ (oneto (x = x)) idpath))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => concat_1p p).
    + intros ? ? p ; induction p ; cbn.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Definition pUnitor_r_inv
             {X : Type} `{IsTrunc 2 X}
             (x y : X)
    : NaturalTransformation
        1
        (concat_functor x x y o (1 * @const_functor _ (oneto (x = x)) idpath)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + exact (fun p => (concat_1p p)^).
    + intros ? ? p ; induction p.
      refine (concat_1p _ @ (concat_p1 _)^).
  Defined.

  Global Instance pUnitor_r_iso {X : Type} `{IsTrunc 2 X} (x y : X)
    : @IsIsomorphism (oneto (x = y) -> oneto (x = y)) _ _ (pUnitor_r x y).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      induction p ; reflexivity.
  Defined.

  Definition pAssociator
             {X : Type} `{IsTrunc 2 X}
             (w x y z : X)
    : NaturalTransformation
        (concat_functor w x z o (concat_functor x y z, 1))
        (concat_functor w y z o (1, concat_functor w x y)
                        o assoc_prod (oneto (y = z)) (oneto (x = y)) (oneto (w = x))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[p₁ p₂] p₃] ; cbn in *.
      apply concat_p_pp.
    + intros [[p₁ p₂] p₃] [[q₁ q₂] q₃] [[r₁ r₂] r₃] ; cbn in *.
      induction p₁, p₂, p₃ ; cbn.
      rewrite <- r₁, <- r₂, <- r₃ ; cbn.
      reflexivity.
  Defined.

  Definition pAssociator_inv
             {X : Type} `{IsTrunc 2 X}
             (w x y z : X)
    : NaturalTransformation
        (concat_functor w y z o (1, concat_functor w x y)
                        o assoc_prod (oneto (y = z)) (oneto (x = y)) (oneto (w = x)))
        (concat_functor w x z o (concat_functor x y z, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + cbn ; intros [[p q] r].
      apply concat_pp_p.
    + intros [[p₁ p₂] p₃] [[q₁ q₂] q₃] [[r₁ r₂] r₃] ; cbn in *.
      induction p₁, p₂, p₃ ; cbn.
      rewrite <- r₁, <- r₂, <- r₃ ; cbn.
      reflexivity.
  Defined.

  Global Instance pAssociator_iso {X : Type} `{IsTrunc 2 X} (w x y z : X)
    : @IsIsomorphism ((oneto (y = z) * oneto (x = y)) * oneto (w = x)
                      -> oneto (w = z))
                     _ _ (pAssociator w x y z).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply pAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[p₁ p₂] p₃] ; cbn in *.
      induction p₁, p₂, p₃ ; reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [[p₁ p₂] p₃] ; cbn in *.
      induction p₁, p₂, p₃ ; reflexivity.
  Defined.

  Definition twoto (X : Type) `{IsTrunc 2 X} : BiCategory.
  Proof.
    simple refine {|Obj := X ;
             Hom := fun x y => oneto (x = y) ;
             id_m := fun _ => idpath ;
             c_m := concat_functor ;
             un_l := pUnitor_l ;
             un_r := pUnitor_r ;
             assoc := pAssociator|}.
    - intros x y z p q ; cbn in *.
      induction p, q ; cbn.
      reflexivity.
    - cbn ; intros v w x y z s r q p.
      induction p, q, r, s ; cbn.
      reflexivity.
  Defined.
End TwoTypeBiGroupoid.

Section OneTypesBiCategory.
  Context `{Univalence}.

  Definition maps (A B : 1 -Type) : PreCategory.
  Proof.
    simple refine (@Build_PreCategory (A -> B) (fun f g => f = g) _ _ _ _ _ _).
    - reflexivity.
    - intros ? ? ? p q ; exact (q @ p).
    - cbn ; intros.
      apply concat_p_pp.
    - cbn ; intros.
      apply concat_p1.
    - cbn ; intros.
      apply concat_1p.
  Defined.

  Definition maps_cat (A B : 1 -Type) : IsCategory (maps A B).
  Proof.
    intros f g ; cbn in *.
    simple refine (isequiv_adjointify _ _ _ _).
    - intros α.
      apply α.
    - intros α.
      apply path_isomorphic.
      destruct α as [α αiso].
      induction α ; cbn in *.
      reflexivity.
    - intros p ; induction p.
      reflexivity.
  Defined.

  Definition comp_functor
             (A B C : 1 -Type)
    : Functor (maps B C * maps A B) (maps A C).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - exact (fun f => (fst f) o (snd f)).
    - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] ; cbn in *.
      induction h₁, h₂ ; cbn.
      reflexivity.
    - intros [f₁ f₂] [g₁ g₂] [h₁ h₂] [p₁ p₂] [q₁ q₂] ; cbn in *.
      induction p₁, p₂, q₁, q₂ ; cbn.
      reflexivity.
    - intros [f₁ f₂] ; cbn in *.
      reflexivity.
  Defined.

  Definition cUnitor_l
             (A B : 1 -Type)
    : NaturalTransformation
        (comp_functor A B B o (@const_functor _ (maps B B) idmap * 1))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + cbn ; intros ? ? p.
      induction p.
      reflexivity.
  Defined.

  Definition cUnitor_l_inv
             (A B : 1 -Type)
    : NaturalTransformation
        1
        (comp_functor A B B o (@const_functor (maps A B) (maps B B) idmap * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; cbn.
      induction p.
      reflexivity.
  Defined.

  Global Instance cUnitor_l_iso (A B : 1 -Type)
    : @IsIsomorphism (maps A B -> maps A B) _ _ (cUnitor_l A B).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.

  Definition cUnitor_r
             (A B : 1 -Type)
    : NaturalTransformation
        (comp_functor A A B o (1 * @const_functor (maps A B) (maps A A) idmap))
        1.
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; induction p ; cbn.
      reflexivity.
  Defined.

  Definition cUnitor_r_inv
             (A B : 1 -Type)
    : NaturalTransformation
        1
        (comp_functor A A B o (1 * @const_functor (maps A B) (maps A A) idmap)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + reflexivity.
    + intros ? ? p ; induction p ; cbn.
      reflexivity.
  Defined.

  Global Instance cUnitor_r_iso (A B : 1 -Type)
    : @IsIsomorphism (maps A B -> maps A B) _ _ (cUnitor_r A B).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros p ; cbn in *.
      reflexivity.
  Defined.

  Definition cAssociator
             (A B C D : 1 -Type)
    : NaturalTransformation
        (comp_functor A B D o (comp_functor B C D, 1))
        (comp_functor A C D o (1, comp_functor A B C)
                        o assoc_prod (maps C D) (maps B C) (maps A B)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      reflexivity.
  Defined.

  Definition cAssociator_inv
             (A B C D : 1 -Type)
    : NaturalTransformation
        (comp_functor A C D o (1, comp_functor A B C)
                      o assoc_prod (maps C D) (maps B C) (maps A B))
        (comp_functor A B D o (comp_functor B C D, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    + intros [[f₁ f₂] f₃] [[g₁ g₂] g₃] [[h₁ h₂] h₃] ; cbn in *.
      induction h₁, h₂, h₃ ; cbn.
      reflexivity.
  Defined.

  Global Instance cAssociator_iso (A B C D : 1 -Type)
    : @IsIsomorphism ((maps C D * maps B C) * maps A B
                      -> maps A D)
                     _ _ (cAssociator A B C D).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply cAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
    - cbn.
      apply path_natural_transformation.
      intros [[f₁ f₂] f₃] ; cbn in *.
      reflexivity.
  Defined.

  Definition onetypebi : BiCategory.
  Proof.
    simple refine {|Obj := 1 -Type ;
                    Hom := maps ;
                    id_m := fun _ => idmap ;
                    c_m := comp_functor ;
                    un_l := cUnitor_l ;
                    un_r := cUnitor_r ;
                    assoc := cAssociator|}.
    - intros A B C g f ; cbn.
      reflexivity.
    - intros A B C D E k h g f ; cbn.
      reflexivity.
  Defined.
End OneTypesBiCategory.

Section CatBiCategory.
  Context `{Univalence}.
  Definition cat_H (C₁ C₂ : PreCategory) : PreCategory
    := functor_category C₁ C₂.

  Definition comp_funct
             (C₁ C₂ C₃ : PreCategory)
    : Functor (cat_H C₂ C₃ * cat_H C₁ C₂) (cat_H C₁ C₃).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - cbn ; intros [p₁ p₂].
      exact (p₁ o p₂)%functor.
    - intros [F₁ F₂] [G₁ G₂] [r₁ r₂] ; cbn in *.
      exact (whisker_r r₁ G₂ o whisker_l F₁ r₂)%natural_transformation.
    - intros [F₁ F₂] [G₁ G₂] [H₁ H₂] [a₁ a₂] [b₁ b₂] ; cbn in *.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite composition_of.
      rewrite !associativity.
      f_ap.
      rewrite <- !associativity.
      f_ap.
      apply a₁.
    - intros [F₁ F₂].
      cbn in *.
      rewrite NaturalTransformation.Composition.Laws.whisker_r_left_identity.
      rewrite NaturalTransformation.Composition.Laws.whisker_l_right_identity.
      apply NaturalTransformation.Composition.Laws.left_identity.
  Defined.

  Definition nUnitor_l
             (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (comp_funct C₁ C₂ C₂ o (@const_functor (cat_H C₁ C₂) (cat_H C₂ C₂)
                                               (Functor.identity C₂) * 1))
        (Functor.identity (cat_H C₁ C₂)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros C ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite !left_identity, right_identity.
      reflexivity.
  Defined.

  Definition nUnitor_l_inv
             (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (Functor.identity (cat_H C₁ C₂))
        (comp_funct C₁ C₂ C₂ o (@const_functor (cat_H C₁ C₂) (cat_H C₂ C₂)
                                               (Functor.identity C₂) * 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros C ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite !left_identity, right_identity.
      reflexivity.
  Defined.

  Global Instance nUnitor_l_iso (C₁ C₂ : PreCategory)
    : @IsIsomorphism (cat_H C₁ C₂ -> cat_H C₁ C₂) _ _ (nUnitor_l C₁ C₂).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply nUnitor_l_inv.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
  Defined.

  Definition nUnitor_r
             (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (comp_funct C₁ C₁ C₂ o (1 * @const_functor (cat_H C₁ C₂) (cat_H C₁ C₁)
                                                   (Functor.identity C₁)))
        (Functor.identity (cat_H C₁ C₂)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros F ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite identity_of, !left_identity, right_identity.
      reflexivity.
  Defined.

  Definition nUnitor_r_inv
             (C₁ C₂ : PreCategory)
    : @NaturalTransformation
        (cat_H C₁ C₂)
        (cat_H C₁ C₂)
        (Functor.identity (cat_H C₁ C₂))
        (comp_funct C₁ C₁ C₂ o (1 * @const_functor (cat_H C₁ C₂) (cat_H C₁ C₁)
                                                   (Functor.identity C₁))).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros F ; cbn.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros F G a ; cbn.
      apply path_natural_transformation.
      intros x ; cbn.
      rewrite identity_of, left_identity, !right_identity.
      reflexivity.
  Defined.

  Global Instance nUnitor_r_iso (C₁ C₂ : PreCategory)
    : @IsIsomorphism (cat_H C₁ C₂ -> cat_H C₁ C₂) _ _ (nUnitor_r C₁ C₂).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply nUnitor_r_inv.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
    - cbn.
      apply path_natural_transformation.
      intros F ; cbn in *.
      apply path_natural_transformation.
      intros X ; cbn in *.
      apply left_identity.
  Defined.

  Definition nAssociator
             (C₁ C₂ C₃ C₄ : PreCategory)
    : NaturalTransformation
        (comp_funct C₁ C₂ C₄ o (comp_funct C₂ C₃ C₄, 1))
        (comp_funct C₁ C₃ C₄ o (1, comp_funct C₁ C₂ C₃)
                        o assoc_prod (cat_H C₃ C₄) (cat_H C₂ C₃) (cat_H C₁ C₂)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[F₁ F₂] F₃] ; cbn in *.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros [[F₁ F₂] F₃] [[G₁ G₂] G₃] [[f₁ f₂] f₃].
      apply path_natural_transformation ; cbn in *.
      intros x.
      rewrite left_identity, right_identity, composition_of.
      rewrite !associativity.
      reflexivity.
  Defined.

  Definition nAssociator_inv
             (C₁ C₂ C₃ C₄ : PreCategory)
    : NaturalTransformation
        (comp_funct C₁ C₃ C₄ o (1, comp_funct C₁ C₂ C₃)
                    o assoc_prod (cat_H C₃ C₄) (cat_H C₂ C₃) (cat_H C₁ C₂))
        (comp_funct C₁ C₂ C₄ o (comp_funct C₂ C₃ C₄, 1)).
  Proof.
    simple refine (Build_NaturalTransformation _ _ _ _).
    + intros [[F₁ F₂] F₃] ; cbn in *.
      simple refine (Build_NaturalTransformation _ _ _ _).
      * intros X ; cbn.
        apply identity.
      * intros X Y f ; cbn.
        rewrite left_identity, right_identity.
        reflexivity.
    + intros [[F₁ F₂] F₃] [[G₁ G₂] G₃] [[f₁ f₂] f₃].
      apply path_natural_transformation ; cbn in *.
      intros x.
      rewrite left_identity, right_identity, composition_of.
      rewrite !associativity.
      reflexivity.
  Defined.

  Global Instance nAssociator_iso (C₁ C₂ C₃ C₄ : PreCategory)
    : @IsIsomorphism ((cat_H C₃ C₄ * cat_H C₂ C₃) * cat_H C₁ C₂
                      -> cat_H C₁ C₄)
                     _ _ (nAssociator C₁ C₂ C₃ C₄).
  Proof.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply nAssociator_inv.
    - cbn.
      apply path_natural_transformation.
      intros [[F₁ F₂] F₃] ; cbn in *.
      apply path_natural_transformation.
      intros C ; cbn.
      apply left_identity.
    - cbn.
      apply path_natural_transformation.
      intros [[F₁ F₂] F₃] ; cbn in *.
      apply path_natural_transformation.
      intros C ; cbn.
      apply left_identity.
  Defined.

  Definition Cat : BiCategory.
  Proof.
    simple refine
           {|Obj := PreCategory ;
             Hom := cat_H ;
             id_m := _ ;
             c_m := comp_funct ;
             un_l := nUnitor_l ;
             un_r := nUnitor_r ;
             assoc := nAssociator|}.
    - intros C₁ C₂ C₃ F G ; cbn in *.
      apply path_natural_transformation ; cbn.
      intros C.
      rewrite left_identity, right_identity.
      reflexivity.
    - intros C₁ C₂ C₃ C₄ C₅ F₁ F₂ F₃ F₄.
      apply path_natural_transformation.
      intros C ; cbn in *.
      rewrite !identity_of, !left_identity.
      reflexivity.
  Defined.
End CatBiCategory.

Section FullSubBicategory.
  Context `{Univalence}.

  Definition full_sub (C : BiCategory) (P : Obj C -> hProp) : BiCategory
    := {|Obj := {X : Obj C & P X} ;
         Hom := fun X Y => Hom C X.1 Y.1 ;
         id_m := fun X => id_m X.1 ;
         c_m := fun X Y Z => @c_m _ C X.1 Y.1 Z.1 ;
         un_l := fun X Y => un_l X.1 Y.1 ;
         un_l_iso := fun X Y => un_l_iso C X.1 Y.1 ;
         un_r := fun X Y => un_r X.1 Y.1 ;
         un_r_iso := fun X Y => un_r_iso C X.1 Y.1 ;
         assoc := fun W X Y Z => assoc W.1 X.1 Y.1 Z.1 ;
         assoc_iso := fun W X Y Z => assoc_iso C W.1 X.1 Y.1 Z.1 ;
         triangle := fun X Y Z => @triangle _ C X.1 Y.1 Z.1 ;
         pentagon := fun V W X Y Z => @pentagon _ C V.1 W.1 X.1 Y.1 Z.1|}.
End FullSubBicategory.

Section Morphism.
  Context `{Univalence}.
  Local Open Scope bicategory_scope.

  Record LaxFunctor (C D : BiCategory) :=
    {
      Fobj :> Obj C -> Obj D ;
      Fmor : forall {X Y : C}, Functor (Hom C X Y) (Hom D (Fobj X) (Fobj Y)) ;
      Fcomp : forall {X Y Z : C},
          NaturalTransformation
            (c_m o (Functor.pair (@Fmor Y Z) (@Fmor X Y)))
            ((@Fmor X Z) o c_m);
      Fid : forall (X : C), morphism _ (id_m (Fobj X)) (Fmor (id_m X));
      Fun_r : forall {X Y : C} (f : Hom C X Y),
          un_r (Fobj X) (Fobj Y) (Fmor f)
          =
          ((morphism_of Fmor (un_r _ _ f))
             o (Fcomp (f,id_m X))
             o (1 ∗ Fid X))%morphism
          ;
      Fun_l : forall (X Y : C) (f : Hom C X Y),
          un_l (Fobj X) (Fobj Y) (Fmor f)
          =
          ((morphism_of Fmor (un_l X Y f))
             o (Fcomp (id_m Y,f))
             o (Fid Y ∗ 1))%morphism ;
      Fassoc : forall (W X Y Z : C) (h : Hom C Y Z) (g : Hom C X Y) (f : Hom C W X),
          ((Fcomp (h, (g ⋅ f)))
             o (1 ∗ (Fcomp (g,f)))
             o (assoc _ _ _ _
                    (Fmor h,
                     Fmor g,
                     Fmor f))
          =
          (morphism_of Fmor (assoc W X Y Z (h,g,f)))
            o Fcomp (h ⋅ g,f)
            o (Fcomp (h,g) ∗ 1))%morphism
    }.

  Definition laxmorphism_of
             {C D : BiCategory} (F : LaxFunctor C D)
             {X Y : C} : Functor (Hom C X Y) (Hom D (F X) (F Y))
    := Fmor _ _ F.
End Morphism.

Arguments Fmor {_ C D} F {X Y} : rename.
Arguments Fcomp {_ C D} F {X Y Z} : rename.
Arguments Fid {_ C D} F X : rename.

Section test.
  Context `{Univalence}.

  Definition ap_func
             {X Y : Type}
             `{IsTrunc 2 X} `{IsTrunc 2 Y}
             (f : X -> Y)
             {x₁ x₂ : X}
    : Functor (oneto (x₁ = x₂)) (oneto (f x₁ = f x₂)).
  Proof.
    simple refine (Build_Functor _ _ _ _ _ _).
    - cbn.
      exact (ap f).
    - cbn ; intros p q r.
      induction r.
      reflexivity.
    - cbn ; intros p q r s₁ s₂.
      induction s₁, s₂.
      reflexivity.
    - cbn ; intros p.
      reflexivity.
  Defined.

  Definition test
             {X Y : Type}
             `{IsTrunc 2 X} `{IsTrunc 2 Y}
             (f : X -> Y)
    : LaxFunctor (twoto X) (twoto Y).
  Proof.
    simple refine {| Fobj := _ |}.
    - cbn.
      exact f.
    - intros a b ; cbn.
      apply ap_func.
    - cbn.
      intros a b c.
      simple refine (Build_NaturalTransformation _ _ _ _).
      + cbn ; intros [p q].
        apply (ap_pp f q p)^.
      + intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
        induction r₁, r₂ ; cbn.
        induction p₁, p₂ ; reflexivity.
    - intros a ; cbn.
      reflexivity.
    - intros a b p ; cbn in *.
      induction p ; cbn.
      reflexivity.
    - intros a b p ; cbn.
      induction p ; cbn.
      reflexivity.
    - intros a b c d p q r ; cbn.
      induction p, q, r ; cbn.
      reflexivity.
  Defined.
End test.

Section LaxTransformation.
  Context `{Univalence}.

  Local Open Scope bicategory_scope.

  Local Instance un_r_iso_componenetwise {B : BiCategory} {X Y : B} f :
    Morphisms.IsIsomorphism (un_r X Y f).
  Proof.
    unshelve eapply isisomorphism_components_of.
    - apply _.
    - apply un_r_iso.
  Qed.

  Local Instance assoc_iso_componenetwise {B : BiCategory} {W X Y Z : B} f :
    Morphisms.IsIsomorphism (assoc W X Y Z f).
  Proof.
    unshelve eapply isisomorphism_components_of.
    - apply _.
    - apply assoc_iso.
  Qed.

  (* For f ∈ Hom(Y₁,Y₂):
     - f_∗ : Hom(X,Y₁) → Hom(X,Y₂)
     - f^∗ : Hom(Y₂,X) → Hom(Y₁,X)
   *)
  Definition postcomp {C : BiCategory} {Y1 Y2 : C} (f : Hom _ Y1 Y2) (X : C) :
    Functor (Hom _ X Y1) (Hom _ X Y2) := c_m o Functor.prod (const_functor f) 1.
  Definition precomp {C : BiCategory} {Y1 Y2 : C} (f : Hom _ Y1 Y2) (X : C) :
    Functor (Hom _ Y2 X) (Hom _ Y1 X) := c_m o Functor.prod 1 (const_functor f).

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
            o (assoc _ _ _ _ (laxcomponent_of Z, Fmor F g, Fmor F f))
            o (laxnaturality_of g ∗ 1)
            o ((inverse (assoc _ _ _ _))
                 (Fmor G g, laxcomponent_of Y, Fmor F f))
            o (1 ∗ laxnaturality_of f)
            o (assoc _ _ _ _ (Fmor G g, Fmor G f, laxcomponent_of X)))%morphism
    }.

End LaxTransformation.
