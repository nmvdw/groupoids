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
                                      (fun x y => modification x y) _ _ _ _ _ _).
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

  (** If a modification `m` is an isomorphism in the category of lax
      transformations, then each 2-cell `m_A` is an isomorphism
      in D  *)
  Global Instance modification_isomorphism_1 {C D : BiCategory}
        {F G : LaxFunctor C D}
        {η₁ η₂ : LaxTransformation F G}
        (m : modification η₁ η₂) :
    @IsIsomorphism (transformation_category F G) _ _ m ->
    forall A, IsIsomorphism (m A).
  Proof.
    intros [mV Hsect Hretr] A. simpl in *.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - apply (mV A).
    - assert ((comp_modification mV m) A = (mV A o m A))%morphism as <-
          by reflexivity.
      rewrite Hsect. reflexivity.
    - assert ((comp_modification m mV) A = (m A o mV A))%morphism as <-
          by reflexivity.
      rewrite Hretr. reflexivity.
  Defined.

  Global Instance modification_isomorphism_2 {C D : BiCategory}
        {F G : LaxFunctor C D}
        {η₁ η₂ : LaxTransformation F G}
        (m : modification η₁ η₂) :
    (forall A, IsIsomorphism (m A)) ->
    @IsIsomorphism (transformation_category F G) _ _ m.
  Proof.
    intros HmA.
    simple refine (Build_IsIsomorphism _ _ _ _ _ _ _).
    - simpl. simple refine (Build_Modification _ _).
      + intro A. apply ((m A)^-1).
      + intros A B f. simpl.
        pose (α := (G ₁ f) ◅ m A).
        (* for this we need: whisker with an isomorphism => isomorphism *)
        (* 1) precompose both side with Gf ◅ mA
           2) postcompose both sides with mA ▻ Ff *)
        admit.
    - simpl.
      apply path_modification.
      funext x ; simpl.
      rewrite vcomp_left_inverse.
      reflexivity.
    - simpl.
      apply path_modification.
      funext x ; simpl.
      rewrite vcomp_right_inverse.
      reflexivity.
  Admitted.

  Lemma transformations_category_isomorphic {C D : BiCategory}
        (F G : LaxFunctor C D) (η₁ η₂ : LaxTransformation F G) :
    @Isomorphic (transformation_category F G) η₁ η₂ ->
    forall x, (η₁ x <~=~> η₂ x)%category.
  Proof.
    intros [m Hm] A.
    simpl in *.
    simple refine (@Build_Isomorphic _ _ _ (m A) _).
  Defined.

  (* Global Instance transformation_isunivalent {C D : BiCategory} *)
  (*        (F G : LaxFunctor C D) : *)
  (*   IsCategory (transformation_category F G). *)
  (* Proof. *)
  (*   intros η₁ η₂ . simpl in *.     *)
  (*   simple refine (isequiv_adjointify _ _ _ _). *)
  (*   - intros [f [g Hgf Hfg]]. simpl in *. *)
  (*     simple refine (path_sigma' _ _ _). *)
  (*     + assert (forall x, η₁.1 x = η₂.1 x) as Hobj. *)
  (*       { admit. } *)
  (*       Set Printing All. *)
  (*     + admit. (* TODO: change the record into a sigma-type *) *)
End transformation_category.
