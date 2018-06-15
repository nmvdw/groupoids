Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
Require Import bicategory lax_functor two_type.


Definition ap_functor
           `{Univalence}
           {X Y : 2 -Type}
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

Definition ap_functor_pp
           `{Univalence}
           {X Y : 2 -Type}
           (f : X -> Y)
           (a b c : X)
  : NaturalTransformation
      (concat_functor Y (f a) (f b) (f c) o (ap_functor f, ap_functor f))
      (ap_functor f o concat_functor X a b c).
Proof.
  simple refine (Build_NaturalTransformation _ _ _ _).
  - cbn ; intros [p q].
    apply (ap_pp f q p)^.
  - intros [p₁ p₂] [q₁ q₂] [r₁ r₂] ; cbn in *.
    induction r₁, r₂ ; cbn.
    induction p₁, p₂ ; reflexivity.
Defined.

Global Instance ap_functor_pp_iso
       `{Univalence}
       {X Y : 2 -Type}
       (f : X -> Y)
       (a b c : X)
  : @IsIsomorphism (_ -> _) _ _ (ap_functor_pp f a b c).
Proof.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - simple refine (Build_NaturalTransformation _ _ _ _) ; cbn.
    + intros [q p].
      apply ap_pp.
    + intros [q₁ p₁] [q₂ p₂] [r₁ r₂] ; simpl in *.
      induction r₁, r₂, p₁, q₁ ; simpl.
      reflexivity.
  - apply path_natural_transformation.
    intros [q p] ; simpl in *.
    induction p, q.
    reflexivity.
  - apply path_natural_transformation.
    intros [q p] ; simpl in *.
    induction p, q.
    reflexivity.
Defined.

Definition lax_ap_functor_data
           `{Univalence}
           {X Y : 2 -Type}
           (f : X -> Y)
  : LaxFunctor_d (path_bigroupoid X) (path_bigroupoid Y).
Proof.
  simple refine {| Fobj_d := _ |}.
  - cbn.
    exact f.
  - intros a b ; cbn.
    apply ap_functor.
  - cbn.
    apply ap_functor_pp.
  - intros a ; cbn.
    reflexivity.
Defined.

Definition is_lax_ap
           `{Univalence}
           {X Y : 2 -Type}
           (f : X -> Y)
  : is_lax (lax_ap_functor_data f).
Proof.
  repeat split.
  - intros a b p ; cbn in *.
    induction p ; cbn.
    reflexivity.
  - intros a b p ; cbn.
    induction p ; cbn.
    reflexivity.
  - intros a b c d p q r ; cbn.
    induction p, q, r ; cbn.
    reflexivity.
Qed.

Definition lax_ap_functor
           `{Univalence}
           {X Y : 2 -Type}
           (f : X -> Y)
  : LaxFunctor (path_bigroupoid X) (path_bigroupoid Y)
  := (lax_ap_functor_data f;is_lax_ap f).

Global Instance lax_ap_functor_pseudo
       `{Univalence}
       {X Y : 2 -Type}
       (f : X -> Y)
  : is_pseudo_functor (lax_ap_functor f).
Proof.
  simple refine {| Fcomp_iso := _ |}.
Defined.