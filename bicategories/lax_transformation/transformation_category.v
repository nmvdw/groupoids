Require Import HoTT.
From HoTT.Categories Require Import
     Category Functor NaturalTransformation FunctorCategory.
From GR.bicategories.bicategory Require Import bicategory univalent bicategory_laws.
From GR.bicategories Require Import
     lax_functor.lax_functor
     lax_transformation.lax_transformation.
Require Import GR.bicategories.modification.modification.
Require Import GR.bicategories.modification.examples.composition.
Require Import GR.bicategories.modification.examples.identity.

Section transformation_category.
  Context `{Univalence}.

  Definition transformation_category
             {C D : BiCategory}
             (F G : LaxFunctor C D)
    : PreCategory.
  Proof.
    simple refine (@Build_PreCategory (LaxTransformation F G)
                                      (fun x y => Modification x y) _ _ _ _ _ _).
    - apply id_modification.
    - cbn ; intros ? ? ? p q.
      apply (comp_modification p q).
    - cbn ; intros.
      apply path_modification ; cbn.
      funext x.
      apply associativity.
    - cbn ; intros.
      apply path_modification ; cbn.
      funext x.
      apply left_identity.
    - cbn ; intros.
      apply path_modification ; cbn.
      funext x.
      apply right_identity.
  Defined.
End transformation_category.

(** If a modification `m` is an isomorphism in the category of lax
      transformations, then each 2-cell `m_A` is an isomorphism
      in D  *)
Global Instance modification_isomorphism_1 {C D : BiCategory}
       `{Univalence}
       {F G : LaxFunctor C D}
       {η₁ η₂ : LaxTransformation F G}
       (m : Modification η₁ η₂)
       (m_iso : @IsIsomorphism (transformation_category F G) _ _ m)
  : forall A, IsIsomorphism (m A).
Proof.
  intros A.
  destruct m_iso as [mV Hsect Hretr] ; cbn in *.
  simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
  - apply (mV A).
  - assert ((comp_modification mV m) A = (mV A o m A))%morphism as <-.
    { reflexivity. }
    rewrite Hsect.
    reflexivity.
  - assert ((comp_modification m mV) A = (m A o mV A))%morphism as <-.
    { reflexivity. }
    rewrite Hretr.
    reflexivity.
Defined.

Section transformation_category_univalent.
  Context `{Univalence}
          {C D : BiCategory}
          `{LocallyUnivalent D}.
  Variable (F G : LaxFunctor C D).

  Definition iso_modification_to_path
             {η₁ η₂ : LaxTransformation F G}
    : @Isomorphic (transformation_category F G) η₁ η₂ -> η₁ = η₂.
  Proof.
    intros [m m_iso] ; cbn in *.
    simple refine (path_laxtransformation _ _).
    - intros X.
      apply (isotoid _ _ _).
      refine (@Build_Isomorphic _ _ _ (m X) _).
    - intros A B f ; cbn.
      rewrite !eisretr ; simpl.
      apply m.
  Defined.

  Definition mod_component_idtoiso
             {η₁ η₂ : LaxTransformation F G}
             (p : η₁ = η₂)
             (X : C)
    : mod_component
        (@morphism_isomorphic
           _ _ _
           (Category.Morphisms.idtoiso (transformation_category F G) p)) X
      =
      @morphism_isomorphic
        _ _ _
        (Category.Morphisms.idtoiso _ (ap (fun f => laxcomponent_of f X) p)).
  Proof.
    induction p ; cbn.
    reflexivity.
  Qed.

  Global Instance is_category_transformation_category
    : IsCategory (transformation_category F G).
  Proof.
    intros η₁ η₂.
    simple refine (isequiv_adjointify _ _ _ _).
    - exact iso_modification_to_path.
    - intro m.
      apply path_isomorphic.
      apply path_modification.
      funext X.
      rewrite mod_component_idtoiso.
      rewrite ap_laxcomponent_path_laxtransformation.
      rewrite eisretr.
      reflexivity.
    - intro p.
      induction p ; simpl.
      unfold iso_modification_to_path ; simpl.
      apply path_laxtransformation_1.
      intros X.
      rewrite <- (eissect ((@Category.Morphisms.idtoiso _ _ _))).
      f_ap.
      apply path_isomorphic ; simpl.
      reflexivity.
  Qed.
End transformation_category_univalent.