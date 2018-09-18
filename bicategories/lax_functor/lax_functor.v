Require Import HoTT.
From HoTT.Categories Require Import
     Functor NaturalTransformation FunctorCategory.
From GR.bicategories Require Import
     general_category bicategory_laws.

Record LaxFunctor_d
       (C D : BiCategory)
  := Build_LaxFunctor_d
       {
         Fobj_d :> Obj C -> Obj D ;
         Fmor_d : forall (X Y : C), Functor (C⟦X,Y⟧) (D⟦Fobj_d X,Fobj_d Y⟧) ;
         Fcomp₁_d :
           forall {X Y Z : C}
                  (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧),
           Fmor_d Y Z g · Fmor_d X Y f ==> Fmor_d X Z (g · f) ;
         Fid_d : forall (X : C), id₁ (Fobj_d X) ==> Fmor_d _ _ (id₁ X)
       }.

Arguments Build_LaxFunctor_d {C D} Fobj_d Fmor_d Fcomp₁_d Fid_d.
Arguments Fobj_d {C D}.
Arguments Fmor_d {C D} _ X Y.
Local Notation "F '₀d' X" := (Fobj_d F X)%bicategory (at level 60).
Local Notation "F '₁d' f" := (Fmor_d F _ _ f)%bicategory (at level 60).
Local Notation "F '₂d' η" := (morphism_of (Fmor_d F _ _) η)%bicategory (at level 60).
Arguments Fcomp₁_d {C D} _ {X Y Z} g f.
Arguments Fid_d {C D} _ X.

Ltac make_laxfunctor := simple refine (Build_LaxFunctor_d _ _ _ _).

Record is_lax
       {C D : BiCategory}
       (F : LaxFunctor_d C D)
  := Build_is_lax
       {
         Fcomp₂_p :
           forall {X Y Z : C}
                  {g₁ g₂ : C⟦Y,Z⟧} {f₁ f₂ : C⟦X,Y⟧}
                  (η₁ : g₁ ==> g₂)
                  (η₂ : f₁ ==> f₂),
             (Fcomp₁_d F g₂ f₂)
               ∘ ((F ₂d η₁) * (F ₂d η₂))
             =
             (F ₂d (η₁ * η₂))
               ∘ (Fcomp₁_d F g₁ f₁) ;
         F_left_unit_p :
           forall {X Y : C} (f : C⟦X,Y⟧),
             left_unit (F ₁d f)
             =
             (F ₂d (left_unit f))
               ∘ Fcomp₁_d F (id₁ Y) f
               ∘ (Fid_d F Y * id₂ (F ₁d f)) ;
         F_right_unit_p :
           forall {X Y : C} (f : C⟦X,Y⟧),
             right_unit (F ₁d f)
             =
             (F ₂d (right_unit f))
               ∘ Fcomp₁_d F f (id₁ X)
               ∘ (id₂ (F ₁d f) * Fid_d F X) ;
         F_assoc_p :
           forall {W X Y Z : C}
                  (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧),
             (Fcomp₁_d F h (g · f))
               ∘ (id₂ (F ₁d h) * Fcomp₁_d F g f)
               ∘ assoc (F ₁d h) (F ₁d g) (F ₁d f)
             =
             (F ₂d (assoc h g f))
                ∘ Fcomp₁_d F (h · g) f
                ∘ (Fcomp₁_d F h g * id₂ (F ₁d f))
       }.

Arguments Build_is_lax {C D F} _ _ _ _.
Arguments Fcomp₂_p {C D F} _ {X Y Z g₁ g₂ f₁ f₂} η₁ η₂.
Arguments F_left_unit_p {C D F} _ {X Y} f.
Arguments F_right_unit_p {C D F} _ {X Y} f.
Arguments F_assoc_p {C D F} _ {W X Y Z} h g f.

Ltac make_is_lax := simple refine (Build_is_lax _ _ _ _).

Definition LaxFunctor (C D : BiCategory)
  := {F : LaxFunctor_d C D & is_lax F}.

Definition Build_LaxFunctor
           {C D : BiCategory}
           (F : LaxFunctor_d C D)
           (F_lax : is_lax F)
  : LaxFunctor C D
  := (F;F_lax).

Definition Fobj
           {C D : BiCategory}
           (F : LaxFunctor C D)
  : C -> D
  := Fobj_d F.1.

Coercion Fobj : LaxFunctor >-> Funclass.

Definition Fmor
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (X Y : C)
  : Functor (C⟦X,Y⟧) (D⟦F X, F Y⟧)
  := Fmor_d F.1 X Y.

Notation "F '₁' f" := (Fmor F _ _ f) (at level 40) : bicategory_scope.
Notation "F '₂' η" := (morphism_of (Fmor F _ _) η) (at level 40) : bicategory_scope.

Definition Fmor₂_id₂
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : F ₂ (id₂ f) = id₂ (F ₁ f).
Proof.
  apply Fmor.
Defined.

Definition Fmor₂_vcomp
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y : C}
           {f g h : C⟦X,Y⟧}
           (η₁ : f ==> g) (η₂ : g ==> h)
  : F ₂ (η₂ ∘ η₁) = (F ₂ η₂) ∘ (F ₂ η₁).
Proof.
  apply Fmor.
Defined.

Definition Fmor₂_inverse
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y : C}
           {f g : C⟦X,Y⟧}
           (α : f ==> g)
           `{IsIsomorphism _ _ _ α}
  : F ₂ (α^-1) = (F ₂ α)^-1.
Proof.
  apply inverse_of.
Qed.

Definition Fcomp₁
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : (F ₁ g) · (F ₁ f) ==> (F ₁ (g · f))
  := Fcomp₁_d F.1 g f.

Definition Fcomp₂
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y Z : C}
           {f₁ f₂ : C⟦X,Y⟧}
           {g₁ g₂ : C⟦Y,Z⟧}
           (η₁ : g₁ ==> g₂)
           (η₂ : f₁ ==> f₂)
  : Fcomp₁ F g₂ f₂ ∘ ((F ₂ η₁) * (F ₂ η₂)) = (F ₂ (η₁ * η₂)) ∘ Fcomp₁ F g₁ f₁
  := Fcomp₂_p F.2 η₁ η₂.

Definition Fcomp
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (X Y Z : C)
  : NaturalTransformation
      ((hcomp (F X) (F Y) (F Z))
         o (Functor.pair (Fmor F Y Z) (Fmor F X Y)))
      ((Fmor F X Z) o hcomp X Y Z).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - intros [g f] ; simpl in *.
    apply Fcomp₁.
  - intros [f₁ f₂] [g₁ g₂] [η₁ η₂] ; simpl in *.
    apply Fcomp₂.
Defined.

Definition Fid
           {C D : BiCategory}
           (F : LaxFunctor C D)
           (X : C)
  : id₁ (F X) ==> (F ₁ (id₁ X))
  := Fid_d F.1 X.

Definition F_left_unit
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : left_unit (F ₁ f)
    =
    (F ₂ (left_unit f))
      ∘ Fcomp₁ F (id₁ Y) f
      ∘ ((Fid F Y) * (id₂ (F ₁ f)))
  := F_left_unit_p F.2 f.

Definition F_right_unit
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {X Y : C}
           (f : C⟦X,Y⟧)
  : right_unit (F ₁ f)
    =
    (F ₂ (right_unit f))
      ∘ Fcomp₁ F f (id₁ X)
      ∘ ((id₂ (F ₁ f)) * (Fid F X))
  := F_right_unit_p F.2 f.

Definition F_assoc
           {C D : BiCategory}
           (F : LaxFunctor C D)
           {W X Y Z : C}
           (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧)
  : (Fcomp₁ F h (g · f))
      ∘ ((id₂ (F ₁ h)) * (Fcomp₁ F g f))
      ∘ assoc (F ₁ h) (F ₁ g) (F ₁ f)
    =
    (F ₂ (assoc h g f))
      ∘ Fcomp₁ F (h · g) f
      ∘ ((Fcomp₁ F h g) * (id₂ (F ₁ f)))
  := F_assoc_p F.2 h g f.

Class is_pseudo
      {C D : BiCategory}
      (F : LaxFunctor C D)
  := { Fcomp_iso : forall {X Y Z : C}
                          (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧),
         IsIsomorphism (Fcomp₁ F g f) ;
       Fid_iso : forall {X : C},
         IsIsomorphism (Fid F X)
     }.

Global Instance is_hprop_is_pseudo
       `{Univalence}
       {C D : BiCategory}
       (F : LaxFunctor C D)
  : IsHProp (is_pseudo F).
Proof.
  apply hprop_allpath.
  intros x y.
  destruct x as [x1 x2], y as [y1 y2].
  assert (x1 = y1) as ->.
  { apply path_ishprop. }
  assert (x2 = y2) as ->.
  { apply path_ishprop. }
  reflexivity.
Qed.

Definition PseudoFunctor
           `{Univalence}
           (C D : BiCategory)
  : Type
  := {F : LaxFunctor C D & is_pseudo F}.

Ltac make_pseudo_functor_lax := simple refine (_;_).

Coercion PseudoFunctor_to_LaxFunctor
         `{Univalence}
         {C D : BiCategory}
         (F : PseudoFunctor C D)
  := F.1.

Global Instance ise_pseudo_pseudo_functor
       `{Univalence}
       {C D : BiCategory}
       (F : PseudoFunctor C D)
  : is_pseudo F
  := F.2.

Global Instance Fcomp₁_is_iso
       {C D : BiCategory}
       (F : LaxFunctor C D)
       `{is_pseudo _ _ F}
       {X Y Z : C}
       (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : IsIsomorphism (Fcomp₁ F g f).
Proof.
  apply Fcomp_iso.
Defined.

Definition Fcomp₁_inv
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
           {X Y Z : C}
           (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧)
  : (F ₁ (g · f)) ==> (F ₁ g) · (F ₁ f).
Proof.
  exact (Fcomp₁ F g f)^-1.
Defined.

Global Instance Fcomp_is_iso
       `{Funext}
       {C D : BiCategory}
       (F : LaxFunctor C D)
       `{is_pseudo _ _ F}
       {X Y Z : C}
  : @IsIsomorphism (_ -> _) _ _ (Fcomp F X Y Z).
Proof.
  apply isisomorphism_natural_transformation.
  apply _.
Defined.

Definition Fcomp₁_inv_naturality
           `{Funext}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
           {X Y Z : C}
           {g₁ g₂ : C⟦Y,Z⟧} {f₁ f₂ : C⟦X,Y⟧}
           (ηg : g₁ ==> g₂) (ηf : f₁ ==> f₂)
  : Fcomp₁_inv F g₂ f₂ ∘ (F ₂ (ηg * ηf))
    =
    ((F ₂ ηg) * (F ₂ ηf)) ∘ Fcomp₁_inv F g₁ f₁
  := commutes (@morphism_inverse (_ -> _) _ _ (Fcomp F X Y Z) _) (g₁,f₁) (g₂,f₂) (ηg,ηf).

Global Instance Fid_is_iso
       {C D : BiCategory}
       (F : LaxFunctor C D)
       `{is_pseudo _ _ F}
       {X : C}
  : IsIsomorphism (Fid F X).
Proof.
  apply Fid_iso.
Defined.

Definition Fid_inv
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
           (X : C)
  : (F ₁ (id₁ X)) ==> id₁ (F X).
Proof.
  exact (Fid F X)^-1.
Defined.

Definition F_left_unit_inv
           `{Funext}
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : left_unit_inv (F ₁ f)
    =
    ((Fid_inv F Y) * (id₂ (F ₁ f)))
      ∘ Fcomp₁_inv F (id₁ Y) f
      ∘ (F ₂ (left_unit_inv f)).
Proof.
  rewrite <- !inverse_of_left_unit.
  unfold Fcomp₁_inv, Fid_inv.
  rewrite <- id₂_inverse.
  rewrite Fmor₂_inverse.
  rewrite <- hcomp_inverse.
  rewrite <- !vcomp_inverse.
  apply path_inverse_2cell.
  rewrite <- !vcomp_assoc.
  apply F_left_unit.
Qed.

Definition F_right_unit_inv
           {C D : BiCategory}
           (F : LaxFunctor C D)
           `{is_pseudo _ _ F}
           {X Y : C}
           (f : C⟦X,Y⟧)
  : right_unit_inv (F ₁ f)
    =
    ((id₂ (F ₁ f)) * (Fid_inv F X))
      ∘ Fcomp₁_inv F f (id₁ X)
      ∘ (F ₂ (right_unit_inv f)).
Proof.
  rewrite <- !inverse_of_right_unit.
  unfold Fcomp₁_inv, Fid_inv.
  rewrite <- id₂_inverse.
  rewrite Fmor₂_inverse.
  rewrite <- hcomp_inverse.
  rewrite <- !vcomp_inverse.
  apply path_inverse_2cell.
  rewrite <- !vcomp_assoc.
  apply F_right_unit.
Qed.

Record PseudoFunctor_d
       (C D : BiCategory)
  := Build_PseudoFunctor_d
       {
         PObj :> C -> D ;
         POne : forall {X Y : C},
             C⟦X,Y⟧ -> D⟦PObj X,PObj Y⟧ ;
         PTwo : forall {X Y : C} {f g : C⟦X,Y⟧},
             f ==> g -> (POne f) ==> (POne g) ;
         Pcomp_d : forall {X Y Z : C}
                           (g : C⟦Y,Z⟧)
                           (f : C⟦X,Y⟧),
             POne g · POne f ==> POne (g · f) ;
         Pid_d : forall (X : C),
             id₁ (PObj X) ==> POne (id₁ X) ;
         Pcomp_inv_d : forall {X Y Z : C}
                               (g : C⟦Y,Z⟧)
                               (f : C⟦X,Y⟧),
             POne (g · f) ==> POne g · POne f ;
         Pid_inv_d : forall (X : C),
             POne (id₁ X) ==> id₁ (PObj X)
       }.

Arguments Build_PseudoFunctor_d {C D} _ _ _ _ _ _ _.
Ltac make_pseudo_functor := simple refine (Build_PseudoFunctor_d _ _ _ _ _ _ _).
Arguments PObj {C D} _ _.
Arguments POne {C D} _ {X Y} _.
Arguments PTwo {C D} _ {X Y f g} _%bicategory.
Arguments Pcomp_d {C D} _ {X Y Z} g f.
Arguments Pid_d {C D} _ X.
Arguments Pcomp_inv_d {C D} _ {X Y Z} g f.
Arguments Pid_inv_d {C D} _ X.
Bind Scope bicategory_scope with PseudoFunctor_d.

Record is_pseudo_functor_p
       {C D : BiCategory}
       (F : PseudoFunctor_d C D)
  := Build_is_pseudo_functor {
         PTwo_id₂ : forall (X Y : C)
                           (f : C⟦X,Y⟧),
           PTwo F (id₂ f) = id₂ (POne F f) ;
         PTwo_comp :
           forall {X Y : C}
                  {f g h : C⟦X,Y⟧}
                  (η : f ==> g)
                  (ε : g ==> h),
             PTwo F (ε ∘ η) = PTwo F ε ∘ PTwo F η ;
         Pcomp_natural :
           forall {X Y Z : C}
                  {f₁ f₂ : C⟦X,Y⟧}
                  {g₁ g₂ : C⟦Y,Z⟧}
                  (η₁ : f₁ ==> f₂)
                  (η₂ : g₁ ==> g₂),
             Pcomp_d F g₂ f₂ ∘ ((PTwo F η₂) * (PTwo F η₁))
             =
             PTwo F (η₂ * η₁) ∘ Pcomp_d F g₁ f₁ ;
         Pright_unit :
           forall {X Y : C}
                  (f : C⟦X,Y⟧),
             right_unit (POne F f)
             =
             (PTwo F (right_unit f))
               ∘ Pcomp_d F f (id₁ X)
               ∘ (id₂ (POne F f) * Pid_d F X) ;
         Pleft_unit :
           forall {X Y : C}
                  (f : C⟦X,Y⟧),
             left_unit (POne F f)
             =
             (PTwo F (left_unit f))
               ∘ Pcomp_d F (id₁ Y) f
               ∘ ((Pid_d F Y) * (id₂ (POne F f))) ;
         Passoc :
           forall {W X Y Z : C}
                  (h : C⟦Y,Z⟧) (g : C⟦X,Y⟧) (f : C⟦W,X⟧),
             (Pcomp_d F h (g · f))
               ∘ ((id₂ (POne F h)) * (Pcomp_d F g f))
               ∘ assoc (POne F h) (POne F g) (POne F f)
             =
             (PTwo F (assoc h g f))
               ∘ Pcomp_d F (h · g) f
               ∘ ((Pcomp_d F h g) * (id₂ (POne F f))) ;
         Pcomp_left :
           forall {X Y Z : C}
                  (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧),
             Pcomp_inv_d F g f ∘ Pcomp_d F g f = id₂ (POne F g · POne F f) ;
         Pcomp_right :
           forall {X Y Z : C}
                  (g : C⟦Y,Z⟧) (f : C⟦X,Y⟧),
             Pcomp_d F g f ∘ Pcomp_inv_d F g f = id₂ (POne F (g · f)) ;
         Pid_left :
           forall (X : C),
             Pid_d F X ∘ Pid_inv_d F X = id₂ (POne F (id₁ X)) ;
         Pid_right :
           forall (X : C),
             Pid_inv_d F X ∘ Pid_d F X = id₂ (id₁ (F X))
       }.

Ltac make_is_pseudo := simple refine (Build_is_pseudo_functor _ _ _ _ _ _ _ _ _ _ _ _ _).

Definition Build_PseudoFunctor
           `{Univalence}
           {C D : BiCategory}
           (F : PseudoFunctor_d C D)
           (HF : is_pseudo_functor_p F)
    : PseudoFunctor C D.
Proof.
  simple refine (_;_).
  - simple refine (Build_LaxFunctor _ _).
    + make_laxfunctor.
      * exact (PObj F).
      * intros X Y.
        simple refine (Build_Functor _ _ _ _ _ _).
        ** exact (POne F).
        ** exact (@PTwo _ _ F X Y).
        ** apply HF.
        ** apply HF.
      * intros X Y Z g f ; simpl in *.
        exact (Pcomp_d F g f).
      * exact (Pid_d F).
    + make_is_lax ; intros ; simpl in * ; apply HF.
  - split.
    + intros X Y Z g f.
      simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
      * exact (Pcomp_inv_d F g f).
      * apply HF.
      * apply HF.
    + intros X.
      simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
      * exact (Pid_inv_d F X).
      * apply HF.
      * apply HF.
Defined.