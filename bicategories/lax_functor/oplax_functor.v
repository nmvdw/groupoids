Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category
     bicategory.bicategory
     lax_functor.lax_functor
     lax_functor.examples.identity
     lax_functor.examples.composition
     bicategory.examples.opposite_2.

Definition OpLaxFunctor (C D : BiCategory)
  : Type
  := LaxFunctor (op2 C) (op2 D).

Definition opFobj
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
  : C -> D
  := Fobj F.

Coercion opFobj : OpLaxFunctor >-> Funclass.

Definition opFmor
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           (X Y : C)
  : Functor (C⟦X,Y⟧) (D⟦F X, F Y⟧).
Proof.
  pose (Fmor F X Y) as FmorF.
  cbn in *.
  simple refine (Build_Functor _ _ _ _ _ _).
  - intros f.
    exact (FmorF f).
  - intros f₁ f₂ η ; simpl in *.
    exact (morphism_of FmorF η).
  - intros ; apply FmorF.
  - intros ; apply FmorF.
Defined.

Notation "F 'o₁' f" := (opFmor F _ _ f) (at level 60) : bicategory_scope.
Notation "F 'o₂' η" := (morphism_of (opFmor F _ _) η) (at level 60) : bicategory_scope.

Definition opFmor₂_id₂
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : F o₂ (id₂ f) = id₂ (F o₁ f).
Proof.
  apply opFmor.
Defined.

Definition opFmor₂_vcomp
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : g ==> h)
  : F o₂ (η₂ ∘ η₁) = (F o₂ η₂) ∘ (F o₂ η₁).
Proof.
  apply opFmor.
Defined.

Definition opFcomp₁
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : morphism (Hom D (F X) (F Z)) (F o₁ (g · f)) ((F o₁ g) · (F o₁ f))
  := Fcomp₁ F g f.

Definition opFcomp₂
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           {X Y Z : C}
           {f₁ f₂ : C⟦X,Y⟧}
           {g₁ g₂ : C⟦Y,Z⟧}
           (η₁ : g₁ ==> g₂)
           (η₂ : f₁ ==> f₂)
  : (F o₂ η₁) * (F o₂ η₂) ∘ opFcomp₁ F g₁ f₁
    =
    opFcomp₁ F g₂ f₂ ∘ (F o₂ (η₁ * η₂))
  := Fcomp₂ F η₁ η₂.

Definition opFcomp
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           (X Y Z : C)
  : NaturalTransformation
      ((opFmor F X Z) o hcomp X Y Z)
      ((hcomp (F X) (F Y) (F Z))
         o (Functor.pair (opFmor F Y Z) (opFmor F X Y))).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros [g f] ; simpl in *.
    apply opFcomp₁.
  - intros [f₁ f₂] [g₁ g₂] [η₁ η₂] ; simpl in *.
    exact (Fcomp₂ F η₁ η₂)^.
Defined.

Definition opFid
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           (X : C)
  : morphism (Hom D _ _) (F ₁ (id₁ X)) (id₁ (F X))
  := Fid F X.

Definition opF_left_unit
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : left_unit_inv (F o₁ f)
    =
    (F ₂ (left_unit_inv f)) ∘ (opFcomp₁ F (id₁ Y) f) ∘ (opFid F Y) * (id₂ (F o₁ f))
  := F_left_unit F f.

Definition opF_right_unit
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : right_unit_inv (F o₁ f)
    =
    (F ₂ (right_unit_inv f))
      ∘ opFcomp₁ F f (id₁ X)
      ∘ ((id₂ (F o₁ f)) * (Fid F X))
  := F_right_unit F f.

Definition opF_assoc
           {C D : BiCategory}
           (F : OpLaxFunctor C D)
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (Fcomp₁ F h (g · f))
      ∘ ((id₂ (F ₁ h)) * (Fcomp₁ F g f))
      ∘ assoc_inv (F o₁ h) (F o₁ g) (F o₁ f)
    =
    (F ₂ (assoc_inv h g f))
      ∘ Fcomp₁ F (h · g) f
      ∘ ((Fcomp₁ F h g) * (id₂ (F o₁ f)))
  := F_assoc F h g f.

Definition pseudo_to_oplax_d
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
  : LaxFunctor_d (op2 C) (op2 D).
Proof.
  make_laxfunctor.
  - exact (Fobj F).
  - intros X Y ; cbn in *.
    simple refine (Build_Functor _ _ _ _ _ _).
    + exact (fun f => F ₁ f).
    + exact (fun _ _ α => F ₂ α).
    + intros ? ? ? m₁ m₂ ; simpl in *.
      exact (Fmor₂_vcomp F m₂ m₁).
    + intros f ; simpl in *.
      exact (Fmor₂_id₂ F f).
  - intros X Y Z g f ; simpl in *.
    exact ((Fcomp₁ F g f)^-1)%morphism.
  - intros X ; simpl in *.
    exact ((Fid F X)^-1)%morphism.
Defined.

Definition pseudo_to_oplax_is_oplax
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
  : is_lax (pseudo_to_oplax_d F).
Proof.
  make_is_lax.
  - intros ; simpl.
    unfold vcomp ; simpl.
    apply iso_moveR_pV.
    rewrite associativity.
    apply iso_moveL_Vp.
    apply F.
  - intros X Y f ; cbn in *.
    rewrite <- !inverse_of_left_unit, inverse_of, <- inverse_id, <- hcomp_inverse.
    rewrite <- !inverse_compose.
    apply path_inverse.
    apply F.
  - intros X Y f ; cbn in *.
    rewrite <- !inverse_of_right_unit, inverse_of, <- inverse_id, <- hcomp_inverse.
    rewrite <- !inverse_compose.
    apply path_inverse.
    apply F.
  - intros W X Y Z h g f ; cbn in *.
    rewrite <- !inverse_of_assoc, inverse_of, <- !inverse_id, <- !hcomp_inverse.
    rewrite <- !inverse_compose.
    apply path_inverse.
    apply F.
Qed.

Definition pseudo_to_oplax
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
  : OpLaxFunctor C D
  := Build_LaxFunctor (pseudo_to_oplax_d F) (pseudo_to_oplax_is_oplax F).

Definition oplax_id_functor (C : BiCategory) : OpLaxFunctor C C
  := pseudo_to_oplax (lax_id_functor C).

Definition oplax_comp
           {C D E : BiCategory}
           (G : OpLaxFunctor D E) (F : OpLaxFunctor C D)
  : OpLaxFunctor C E
  := lax_comp G F.